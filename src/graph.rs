//! A graph of program objects which can be reduced by doing some computation
//! which they describe. Also a heap for storing them.

use crate::machine::*;

use arc_swap::ArcSwapOption;
use either::Either;
use joinery::JoinableIterator;
use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::fmt;
use std::fmt::{Display, Formatter as Fmt, Result as FR};
use std::mem::ManuallyDrop as MD;
use std::ptr::NonNull;
use std::rc::{Rc, Weak};
use std::sync::Arc;
use tracing::{error, info, instrument, span, trace, Level};

use crate::machine::{MResult, Primitive};

/// A ref in our system is the basic value unit that is passed everywhere. It is
/// in actuality a 61-bit tagged pointer, where the 61 bits are sometimes
/// interpretered as a number or builtin depending on context. The pointer
/// value refers to some incinerator heap.
#[derive(Clone, Copy, PartialEq)]
pub struct Ref {
    pub(crate) value: u64,
}

impl Ref {
    pub fn decode(self) -> (RefTag, u64) {
        let (tag, nottag) = (self.value & 0b111, self.value & !0b111);
        // SAFETY: all 8 values of RefTag are valid
        unsafe { (core::mem::transmute(tag as u8), nottag) }
    }
    pub unsafe fn pack(tagvalue: RefTag, data: u64) -> Ref {
        debug_assert!(data & 0b111 == 0);
        Ref {
            value: data | tagvalue as u64,
        }
    }

    pub fn prim(prim: Primitive) -> Ref {
        unsafe { Ref::pack(RefTag::Builtin, prim as u64) }
    }

    pub fn deref(&self) -> TaggedObjView {
        let (tag, pointer) = self.decode();
        use RefTag::*;
        match tag {
            SmallNum => TaggedObjView::SmallNum(pointer as u32),
            Builtin => Primitive::try_from(pointer as u32)
                .map(TaggedObjView::Builtin)
                .expect("who put a bad primitive value there?"),
            Data | Extended | Thunk | Pair | Symbol | Partial => unsafe {
                // SAFETY: we only pack direct objdata gc pointers into Ref
                let actual_pointer = pointer as usize as *mut ObjData;
                (*actual_pointer).view(tag)
            },
        }
    }
    pub fn num(self) -> MResult<Arc<num::BigInt>> {
        match self.deref() {
            TaggedObjView::SmallNum(n) => Ok(Arc::new(n.into())),
            TaggedObjView::BigNum(n) => Ok(n.clone()),
            _ => crate::machine::err(crate::machine::EngineErrorKind::TypeMismatch {
                expected: Ty::Num,
                found: self,
                when: "expecting a number",
            }),
        }
    }
}

impl fmt::Debug for Ref {
    fn fmt(&self, f: &mut Fmt) -> FR {
        write!(f, "{:?}", self.deref())
    }
}

impl fmt::Display for Ref {
    fn fmt(&self, f: &mut Fmt) -> FR {
        write!(f, "{}", self.deref())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefTag {
    Extended = 0,
    Thunk,
    SmallNum,
    Data,
    Builtin,
    Symbol,
    Partial,
    Pair,
}

// TODO: support mutation (which can change tags) by enqueueing the mutation,
#[derive(Copy, Clone)]
pub enum TaggedObjView<'a> {
    /// Unevaluated applicative form
    Thunk(&'a ThunkData),
    /// A small number (currently unused)
    SmallNum(u32),
    /// Some tagged data
    Data(&'a TaggedData),
    /// A builtin command of some kind
    Builtin(Primitive),
    /// A named definition
    Symbol(&'a ThunkData, &'a Arc<String>),
    /// A partially applied applicative form, waiting for more arguments before
    /// reduction can proceed.
    Partial(&'a PartialData),
    /// A pair of objects
    Pair(Ref, Ref),
    FreeVariable(&'a Arc<String>),
    /// It is a mystery to everybody (except presumably whoever is driving the runtime)
    Mystery(u32),
    /// A big number
    BigNum(&'a Arc<num::BigInt>),
    /// A statically known function definition
    Fun(&'a FunDef),
    Blackhole,
}

// if the bottom bits are 0, that means it's a reference into the object heap!
// we can use the atom directly as an offset into some (possibly 64-bit) host
// pointer.

/// Meanwhile, expressions! Expressions have all the control flow etc. In a
/// richer language we would have expressions for things like pattern matching in
/// here. As it is, atoms and invocations of atoms to lists of atoms. Applicative
/// forms, the essential core of the system! It's either an object of some kind
/// (`Ref`), which possibly needs further reduction, or else it's an application
/// of some head to some args, with some arity.
#[derive(Clone, PartialEq)]
pub enum ApplicativeForm {
    /// An object of some kind.
    Ref(Ref),
    /// An application of some head to some args. It's actually pretty flexible
    /// about what it means to "apply" something, but not to the extent that you
    /// can provide an arbitrary Applicative instance... yet?
    Apply(Ref, Arity, RefList),
}

#[derive(Debug, PartialEq, Clone, Copy)]
/// Our system records how many args a function has vs needs.
pub enum Arity {
    /// We have no idea. This happens a lot.
    Unk,
    /// We know the arity! This happens less frequently (never, actually, in combinator subset)
    N(u16),
}

#[derive(Debug)]
pub struct Heap {
    gc: Arc<incinerator::HeapRegistration<RefTag>>,
    functions_storage: HashMap<Arc<String>, FunDef>,
}

impl Heap {
    pub fn new() -> Heap {
        todo!()
    }
    pub fn thunk(&self, ap: ApplicativeForm) -> Ref {
        let new_td = ArcSwapOption::from_pointee(Either::Left(ap));
        self.allocate(
            RefTag::Thunk,
            ObjData {
                thunk: MD::new(ThunkData(new_td)),
            },
        )
    }

    pub fn num(&self, n: Arc<num::BigInt>) -> Ref {
        self.allocate(
            RefTag::Extended,
            ObjData {
                extended: MD::new(ExtendedData::BigNum(n)),
            },
        )
    }

    pub fn allocate(&self, tag: RefTag, obj: ObjData) -> Ref {
        // SAFETY:
        unsafe {
            match self.gc.alloc(obj) {
                Some((body_ptr, _header_ptr)) => Ref::pack(tag, body_ptr.as_ptr() as usize as u64),
                None => panic!("oom!"),
            }
        }
    }

    /// Produce a new object, the partial application of `func` to `args`.
    pub fn partially_apply(&self, func: Ref, args: RefList) -> Ref {
        self.allocate(
            RefTag::Partial,
            ObjData {
                partial: MD::new(PartialData { func, args }),
            },
        )
    }

    pub fn symbol(&self, slot: ThunkData, name: Arc<String>) -> Ref {
        self.allocate(
            RefTag::Symbol,
            ObjData {
                symbol: MD::new((slot, name)),
            },
        )
    }

    pub fn aa(&self, lhs: Ref, rhs: Ref) -> ApplicativeForm {
        ApplicativeForm::Apply(lhs, Arity::Unk, smallvec::smallvec![rhs])
    }

    pub fn ea(&self, lhs: ApplicativeForm, rhs: Ref) -> ApplicativeForm {
        match lhs {
            ApplicativeForm::Ref(at) => {
                ApplicativeForm::Apply(at, Arity::Unk, smallvec::smallvec![rhs])
            }
            ApplicativeForm::Apply(at, ar, mut args) => {
                args.push(rhs);
                ApplicativeForm::Apply(at, ar, args)
            }
        }
    }

    pub fn ee(&self, lhs: ApplicativeForm, rhs: ApplicativeForm) -> ApplicativeForm {
        match rhs {
            ApplicativeForm::Ref(at) => self.ea(lhs, at),
            rhs => self.ea(lhs, self.thunk(rhs)),
        }
    }

    pub fn ae(&self, lhs: Ref, rhs: ApplicativeForm) -> ApplicativeForm {
        match rhs {
            ApplicativeForm::Ref(at) => self.aa(lhs, at),
            rhs => self.aa(lhs, self.thunk(rhs)),
        }
    }
}

impl ThunkData {
    pub fn take_thunk(&self) -> Option<ApplicativeForm> {
        //self.0.swap(None).as_ref().and_then(|v| v.as_ref().left().clone())
        todo!()
    }
    pub fn completed(&self) -> Option<Ref> {
        //self.0.load().as_ref().and_then(|v| v.as_ref().right())
        todo!()
    }
    pub fn finish_result(&self, val: Ref) {
        self.0.store(Some(Arc::new(Either::Right(val))));
    }
    pub fn needs_forcing(&self) -> bool {
        //self.0.load().map_or(true, |v| v.is_left())
        todo!()
    } // thunks we're unthunking are still in need of forcing
}

#[derive(Debug, Clone)]
pub struct PartialData {
    pub func: Ref,
    pub args: RefList,
}

pub struct TaggedData {
    pub tag: u32,
    pub body_start: u64,
}

#[derive(Debug, Clone)]
/// A none is sub'd into the heap during evaluation of the thunk so we can start
/// freeing things immediately, and also so that if we encounter an
/// evaluating-thunk we know that we just hit an infinite recursion and need to
/// stop. After the thunk is evaluated, the result is written here, that way
/// everyone sharing this thunk can benefit.
pub struct ThunkData(pub(crate) ArcSwapOption<Either<ApplicativeForm, Ref>>);

#[derive(Clone)]
pub enum ExtendedData {
    FreeVariable(Arc<String>),
    /// For some reason we needed a heap slot to store this value, which fits in a ref.
    Refworthy(Ref),
    Mystery(u32),
    /// A big number
    BigNum(Arc<num::BigInt>),
    Fun(FunDef),
    Blackhole,
}

#[repr(align(8))]
pub union ObjData {
    pub thunk: MD<ThunkData>,
    pub data: TaggedData,
    pub symbol: MD<(ThunkData, Arc<String>)>,
    pub partial: MD<PartialData>,
    pub pair: (Ref, Ref),
    pub extended: MD<ExtendedData>,
}

impl fmt::Debug for ObjData {
    fn fmt(&self, f: &mut Fmt) -> FR {
        todo!()
    }
}

impl ObjData {
    fn view(&self, tag: RefTag) -> TaggedObjView {
        use RefTag::*;
        // SAFETY: by the time we go to view an object it has been fully initialized.
        unsafe {
            match tag {
                Thunk => TaggedObjView::Thunk(&*self.thunk),
                Pair => {
                    let (l, r) = self.pair;
                    TaggedObjView::Pair(l, r)
                }
                Symbol => {
                    let (thunk, symname) = &*self.symbol;
                    TaggedObjView::Symbol(thunk, symname)
                }
                Partial => TaggedObjView::Partial(&*self.partial),
                Data => TaggedObjView::Data(&self.data),
                Extended => match &*self.extended {
                    ExtendedData::FreeVariable(n) => TaggedObjView::FreeVariable(n),
                    ExtendedData::Refworthy(rf) => rf.deref(),
                    ExtendedData::Mystery(n) => TaggedObjView::Mystery(*n),
                    ExtendedData::BigNum(n) => TaggedObjView::BigNum(n),
                    ExtendedData::Fun(fundef) => TaggedObjView::Fun(fundef),
                    ExtendedData::Blackhole => TaggedObjView::Blackhole,
                },
                SmallNum | Builtin => unreachable!("handled by Ref::deref"),
            }
        }
    }
}

/// Reference to a defined function. It knows how long its args are.
#[derive(Clone, PartialEq, Debug)]
pub struct FunDef {
    pub body: Arc<ApplicativeForm>,
    /// the number of arguments this fundef needs before it can evaluated in a
    /// single step to something that isn't a Partial. if the function as defined
    /// is itself a partial function, then the arity here will be the arity of
    /// the wrapped partial
    pub arity: u64,
}

pub type RefList = smallvec::SmallVec<[Ref; 2]>;

impl fmt::Debug for TaggedObjView<'_> {
    fn fmt(&self, f: &mut Fmt) -> FR {
        // todo: try and retrieve heap from illicit, use that to derefs?
        use TaggedObjView::*;
        match self {
            Symbol(_, n) => write!(f, "{}", n),
            Thunk(td) => match &*td.0.load() {
                Some(either) => match &**either {
                    Either::Left(_) => write!(f, "THUNK"),
                    Either::Right(r) => write!(f, "{:?}", r),
                },
                None => write!(f, "(currently evaluating thunk)"),
            },
            SmallNum(n) => write!(f, "{}", n),
            Pair(l, r) => write!(f, "{:?} :: {:?}", l, r),
            Builtin(p) => write!(f, "{:?}", p),
            Partial(pd) => write!(
                f,
                "λ?. ({} {} ?)",
                pd.func,
                pd.args.iter().map(|x| format!("{:?}", x)).join_with(" ")
            ),
            Data(td) => write!(f, "(some opaque data with tag {})", td.tag),
            FreeVariable(s) => write!(f, "{}", s),
            Mystery(tag) => write!(f, "{:?}", tag),
            BigNum(r) => write!(f, "{:?}", r),
            Fun(fd) => write!(f, "(FUN {:?})", fd.body),
            Blackhole => write!(f, ""),
        }
    }
}

impl Display for TaggedObjView<'_> {
    fn fmt(&self, f: &mut Fmt) -> FR {
        write!(f, "{:?}", self)
    }
}

impl TaggedObjView<'_> {
    pub(crate) fn is_value(self) -> bool {
        match self {
            TaggedObjView::Symbol(t, _) | TaggedObjView::Thunk(t) => t.needs_forcing() == false,
            _ => true,
        }
    }
    pub(crate) fn needs_force(self) -> bool {
        match self {
            TaggedObjView::Thunk(t) => true,
            _ => false,
        }
    }
    fn finish_thunk(self, val: Ref) -> Result<(), &'static str> {
        match self {
            TaggedObjView::Thunk(t) => Ok(t.finish_result(val)),
            _ => Err("unthunk a nonthunk?"),
        }
    }
}

impl Primitive {
    fn try_from(v: u32) -> Option<Primitive> {
        // FIXME: enum_derive?
        unsafe { Some(core::mem::transmute(v as u8)) }
    }
}

impl Display for Arity {
    fn fmt(&self, f: &mut Fmt) -> FR {
        match self {
            Arity::Unk => f.write_str("?"),
            Arity::N(n) => n.fmt(f),
        }
    }
}

impl incinerator::Finalize for Ref {}
unsafe impl incinerator::Trace for Ref {
    unsafe fn visit(&self, _heap: &incinerator::Heap<()>, cb: &dyn Fn(&usize)) {
        use RefTag::*;
        let (tag, rawval) = self.decode();
        let ptr_val = rawval as usize;
        match tag {
            Extended | Thunk | Symbol | Partial | Pair => cb(&ptr_val),
            SmallNum | Data | Builtin => (),
        }
    }
    fn finalize_glue(&self) {}
}

impl incinerator::Finalize for ApplicativeForm {}
unsafe impl incinerator::Trace for ApplicativeForm {
    incinerator::custom_trace!(this, {
        match this {
            ApplicativeForm::Ref(rf) => mark!(rf),
            ApplicativeForm::Apply(head, _, args) => {
                mark!(head);
                mark!(&args[..]);
            }
        }
    });
}

impl incinerator::Finalize for ThunkData {}
unsafe impl incinerator::Trace for ThunkData {
    incinerator::custom_trace!(this, {
        if let Some(either) = &*this.0.load() {
            match &**either {
                Either::Left(af) => mark!(af),
                Either::Right(rf) => mark!(rf),
            }
        }
    });
}

impl incinerator::Finalize for ObjData {}
unsafe impl incinerator::Trace for ObjData {
    unsafe fn visit(&self, heap: &incinerator::Heap<()>, cb: &dyn Fn(&usize)) {
        use TaggedObjView::*;
        // SAFETY: this is busted, how should i deal with the inflexibility to
        // tack a generic onto Trace?
        let realheap: &incinerator::Heap<RefTag> = unsafe { core::mem::transmute(heap) };
        macro_rules! mark {
            ($thing:expr) => {
                incinerator::Trace::visit($thing, heap, cb);
            };
        }
        let (seg, idx) =
            realheap.segment_and_idx(NonNull::new_unchecked(self as *const ObjData as *mut u8));
        let hdr = (*seg).header_from_index(idx);
        let reftag = *(*hdr.as_ptr()).data.assume_init_ref();
        match self.view(reftag) {
            Symbol(td, _) | Thunk(td) => mark!(td),
            SmallNum(_) | BigNum(_) | Data(_) | FreeVariable(_) | Mystery(_) | Blackhole
            | Builtin(_) => {}
            Partial(pd) => {
                mark!(&pd.func);
                mark!(&pd.args[..]);
            }
            Pair(l, r) => {
                mark!(&l);
                mark!(&r);
            }
            Fun(fd) => mark!(&*fd.body),
        }
    }

    fn finalize_glue(&self) {}
}
