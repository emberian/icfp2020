//! Implementation limits:
//!
//! Max function args: 2^16
//!
//! Implementation of https://simonmar.github.io/bib/papers/eval-apply.pdf, largely.

use joinery::JoinableIterator;
use smallvec::smallvec;
use std::cell::RefCell;
use std::collections::VecDeque;
use std::fmt;
use std::fmt::{Display, Formatter as Fmt, Result as FR};
use std::mem::ManuallyDrop;
use std::rc::{Rc, Weak};
use std::sync::Arc;
use tracing::{error, info, instrument, span, trace, Level};

pub type MResult<T> = Result<T, EngineError>;

/// A little control monad.
enum StepDone {
    /// Step again, to do more work!
    Again,
    /// Can't evaluate any further (infinite recursion, undefined symbol)
    Stuck,
    /// We're done! The resulting value.
    Complete(Ref),
}

//use crate::graph;
use crate::graph::{
    ApplicativeForm, Arity::*, FunDef, Heap, Ref, RefList, RefTag, TaggedObjView, ThunkData,
};

// General note: the engine requires internal functions to be in "administrative-normal form".
// The types above are like that. It means functions can only be applied to
// atoms, not eg other calls. In order to represent something like (fun x -> x + 1) (4 + 3)
// You must first make a thunk of (4 + 3), and that gives you an atom (as a Ptr) to use.
// The parser handles this.

//#endregion

//#region Machine internal types

/// list forcing state machine state
#[derive(Debug, Clone)]
pub enum ForceListState {
    ReducingHead(Ref),
    ReducingTail,
}
use ForceListState::*;

/// vec forcing state machine state
#[derive(Debug, Clone)]
pub struct ForceArgsState {
    head: Ref,
    args: RefList,
    index_cur: usize,
}

/// Continuation represents the state we need to save across calls etc
#[derive(Debug, Clone)]
pub enum Continuation {
    KIf0(RefList),       // after popping: self.code = branch cond
    UpdThunk(ThunkData), // after popping: variable set to self.code
    Apply(RefList),      // after popping: apply self.code to the args
    #[allow(dead_code)]
    ForceList(ForceListState, Ref), // after popping: Pair originally passed in will be forced thoroughly
    ForceArgs(ForceArgsState), // after popping: top call has had its arguments forced and it can now be applied atomically
}

//#endregion

use Continuation::*;

#[derive(Debug)]
pub struct Engine {
    me: RefCell<Option<Weak<Engine>>>,
    pub state: State,
    /// The expression we most recently called `Engine::eval` with
    toplevel: RefCell<ApplicativeForm>,
}

impl Engine {
    pub fn load_galaxy(&self) -> MResult<()> {
        for line in crate::GALAXY.lines() {
            let (name, value) = crate::parse::cmd(
                line.trim(),
                &self.state.heap,
                &mut *self.state.definitions.borrow_mut(),
            )?;
            self.state.definitions.borrow_mut().insert(name, value);
        }
        Ok(())
    }
    pub fn new() -> Rc<Engine> {
        let rc = Rc::new(Engine {
            me: RefCell::new(None),
            state: State::new(),
            toplevel: RefCell::new(ApplicativeForm::Ref(Ref::prim(Primitive::Nil))),
        });
        *rc.me.borrow_mut() = Some(Rc::downgrade(&rc));
        rc
    }

    pub fn exec(&self, s: &str) -> MResult<Ref> {
        let expr = crate::parse::expr(
            s,
            &self.state.heap,
            &mut *self.state.definitions.borrow_mut(),
        )?;
        self.eval(expr)
    }

    /// This evaluates a single expression. It makes sure to set up an illicit context.
    /// Illicit is kinda implicit args / dependency injection for rust? Anyway it means
    /// we can throw an error anywhere and include rich info from the engine without
    /// having to thread it through literally everything.
    ///
    /// The actual loop is simple enough: apply single steps until a single step errors.
    /// Or, until we're done. At the end, read the result out of the code register.
    pub fn eval(&self, e: ApplicativeForm) -> MResult<Ref> {
        let it_me: Rc<Engine> = self.me.borrow().as_ref().unwrap().upgrade().unwrap();

        // keep it re-entrant

        let old_stack = RefCell::new(vec![]);
        let old_toplevel = RefCell::new(ApplicativeForm::Ref(Ref::prim(Empty)));
        let old_args = RefCell::new(smallvec![]);
        old_toplevel.swap(&self.toplevel);
        old_args.swap(&self.state.arg_storage);
        old_stack.swap(&self.state.stack);

        let loop_result = illicit::Layer::new().offer(it_me).enter(|| {
            let engine = illicit::get::<Rc<Engine>>().expect("who unset the engine??");
            let span = span!(Level::TRACE, "eval", expr = ?e);
            let _enter = span.enter();

            // we push force_list so that when we get back our datum,
            // it contains no laziness.
            let toplevel = engine.state.heap.thunk(e);
            let _ = engine.push(
                ApplicativeForm::Ref(toplevel.clone()),
                ForceList(ReducingTail, toplevel),
                "toplevel eval",
            );

            let mut max = 30;
            loop {
                max -= 1;
                if max == 0 {
                    return Ok(Ref::prim(Primitive::Empty));
                }
                match engine.step() {
                    Ok(StepDone::Again) => {}
                    Ok(StepDone::Stuck) => {
                        // our caller can try and eval this again if they'd like
                        return Ok(self.state.heap.thunk(self.take_code()));
                    }
                    Ok(StepDone::Complete(v)) => return Ok(v),
                    Err(e) => {
                        return Err(e);
                    }
                }
                trace!(
                    "\nstep complete: {:?} ; {:?}\n",
                    expr = engine.state.code.borrow(),
                    args = &*engine.state.arg_storage.borrow()
                );
            }
        });

        self.toplevel.swap(&old_toplevel);
        self.state.arg_storage.swap(&old_args);
        self.state.stack.swap(&old_stack);

        loop_result
    }

    // thought: if i try to evaluate a black hole,
    // that means that there is a UpdThunk _somewhere_
    // on the stack that i need to refer to...

    //#region Single step of core automata loop
    /// Returns Ok(()) if we applied any step
    fn step(&self) -> MResult<StepDone> {
        use crate::graph::TaggedObjView::*;

        // first off, there are argument vectors in the expression if it's a
        // call, and we want to be moving those for most efficient reuse.
        // take it, and replace the code pointer with Empty.
        let code = self.take_code();

        // Ok, let's dig into it, here we'll handle anything that isn't already a value.
        // We return if we hit any of those, so after this match we know we'll have work to do.
        let value = match code {
            ApplicativeForm::Ref(r) => match r.deref() {
                Builtin(_) | SmallNum(_) | Data(_) => r,
                Thunk(t) if t.needs_forcing() => {
                    return self.push(
                        t.take_thunk()
                            .expect("why did we fail to take the thunk if it needed forcing?"),
                        UpdThunk(t.clone()),
                        "THUNK",
                    )
                }
                FreeVariable(n) => match self.state.definitions.borrow().get(n) {
                    Some(def) => {
                        //hobj.store(def.load());
                        if def.needs_forcing() {
                            return self.push(
                                def.take_thunk().expect(
                                    "why did we fail to take the thunk if it needed forcing2?",
                                ),
                                UpdThunk(def.clone()),
                                "FREEVAR",
                            );
                        } else {
                            def.completed()
                                .expect("it should be completed if it doesn't need forcing")
                        }
                    }
                    None => r,
                },
                _ => r,
            },
            ApplicativeForm::Apply(head, arity, args) => {
                return match head.deref() {
                    // the various ways to call various things are not incredibly interesting
                    // in and of themselves. You can read through it if you like.
                    Builtin(p) => self.callfun(head, p.arity() as u64, args),
                    FreeVariable(_) => {
                        let _ = self.goto(
                            ApplicativeForm::Apply(head, arity, args),
                            "uncall symbol repair",
                        );
                        return Ok(StepDone::Stuck);
                    }
                    Fun(fundef) => self.callfun(head, fundef.arity, args),
                    Symbol(_, _) | Thunk(_) => {
                        self.push(ApplicativeForm::Ref(head.clone()), Apply(args), "TCALL")
                    }
                    Partial(data) => {
                        let local_args = data.args.iter().chain(args.iter()).cloned().collect();
                        // FIXME: does this _need_ to be a goto? why? to install the Unk?
                        self.goto(ApplicativeForm::Apply(data.func, Unk, local_args), "PCALL")
                    }
                    Pair(l, r) => {
                        // ap ap cons x0 x1 x2 -> x2 x0 x1
                        self.push(
                            ApplicativeForm::Apply(args[0].clone(), Unk, smallvec![l.clone()]),
                            Apply(smallvec![r.clone()]),
                            "PAIRCALL",
                        )
                    }
                    Mystery(_) | Blackhole | Data(..) => {
                        return err(TypeMismatch {
                            expected: Ty::Callable,
                            found: head.clone(),
                            when: "trying to call",
                        })
                    }
                    SmallNum(_) | BigNum(_) => err(CalledNumber),
                };
            }
        };

        trace!("value is {:?}", value);
        assert!(value.is_value());

        //#region Apply newly produced value to top of control stack if possible.

        // note: we use this : u32 trick to make sure that this match never returns.
        let _: u32 = loop {
            match self.leave() {
                Some(KIf0(ptrs)) => {
                    use std::convert::TryFrom;
                    let smolnum = <usize as TryFrom<&num::BigInt>>::try_from(&*value.num()?);
                    if let Ok(i @ 0) | Ok(i @ 1) = smolnum {
                        return self.goto(ApplicativeForm::Ref(ptrs[i].clone()), "IF0");
                    }
                    return err(EIf0);
                }
                Some(UpdThunk(td)) => {
                    td.finish_result(value.clone());
                    let _ = self.goto(ApplicativeForm::Ref(value), "UPDATE");
                    continue; // this is still a value, safe to do.
                }
                Some(Apply(args)) => {
                    return self.goto(ApplicativeForm::Apply(value, Unk, args), "RETFUN")
                }
                Some(ForceList(ReducingHead(tl), orig)) => {
                    return self.push(
                        ApplicativeForm::Ref(tl),
                        ForceList(ReducingTail, orig),
                        "reduce tail",
                    );
                }
                Some(ForceList(ReducingTail, orig)) => {
                    if let Pair(l, r) = value.deref() {
                        return self.push(
                            ApplicativeForm::Ref(l.clone()),
                            ForceList(ReducingHead(r.clone()), orig),
                            "reduce head",
                        );
                    }
                    return self.goto(ApplicativeForm::Ref(orig), "forcelist done");
                }
                Some(ForceArgs(mut st)) => {
                    st.args[st.index_cur] = value;
                    for (n, starg) in st.args[st.index_cur + 1..].iter_mut().enumerate() {
                        if starg.needs_force() {
                            return self.push(
                                ApplicativeForm::Ref(starg.clone()),
                                ForceArgs(ForceArgsState {
                                    index_cur: st.index_cur + n + 1,
                                    ..st
                                }),
                                "force arg",
                            );
                        }
                    }
                    // alright, we're done here. pack it up and let's make it real
                    // basically this inlines step(goto(Prims(p, args)))
                    match st.head.deref() {
                        Builtin(p) => return self.prim(p, Some(st.args)),
                        _ => return err(Mistake("we forceargs a non-primitive?")),
                    }
                }
                None => return Ok(StepDone::Complete(value)),
            }
        };
        //#endregion
    }

    #[instrument(skip(self))]
    fn prim(&self, p: Primitive, args: Option<RefList>) -> MResult<StepDone> {
        if let Some(args) = args {
            let argstore = RefCell::new(args);
            self.state.arg_storage.swap(&argstore);
            let res = self.evaluate_prim(p)?;
            self.state.arg_storage.swap(&argstore);
            self.goto(res, "PRIM1")
        } else {
            self.goto(self.evaluate_prim(p)?, "PRIM2")
        }
    }

    fn map_num<F>(&self, r: Ref, f: F) -> MResult<Ref>
    where
        F: FnOnce(&mut num::BigInt),
    {
        let mut n = r.num()?;
        f(Arc::make_mut(&mut n));
        Ok(self.state.heap.num(n))
    }
}
//#endregion

/// State of the abstract machine
///
/// All the fields are pub, and also mutable. Behave responsibly with them.
#[derive(Debug)]
pub struct State {
    /// The expression we are attempting to reduce
    pub code: RefCell<ApplicativeForm>,
    /// The control stack, telling us what we need to do after we're done with code
    pub stack: RefCell<Vec<Continuation>>,
    pub heap: Heap,
    /// All top-level symbol definitions.
    pub definitions: RefCell<fnv::FnvHashMap<Arc<String>, ThunkData>>,
    /// The arguments for the currently evaluating function.
    /// Currently, because we only care about those combinator
    /// programs, we never need to refer outside our own stack frame.
    pub arg_storage: RefCell<RefList>,
    /// Map from primitve to a "function declaration" for that primitive, and also a heap cell containing the "function object" for the primitive.
    pub prim_fundefs: RefCell<Vec<Option<(FunDef, Ref)>>>,
}

impl State {
    pub fn new() -> State {
        State {
            code: RefCell::new(ApplicativeForm::Ref(Ref::prim(Primitive::T))),
            stack: RefCell::new(vec![]),
            heap: Heap::new(),
            definitions: RefCell::new(fnv::FnvHashMap::default()),
            arg_storage: RefCell::new(smallvec![]),
            prim_fundefs: RefCell::new(vec![None; 32]), // TODO: size this correctly
        }
    }

    pub fn add_definition(&self, name: Arc<String>, value_slot: ThunkData) {
        self.definitions.borrow_mut().insert(name, value_slot);
    }
}

//#region Engine control methods
// This section is really boring. goto, leave, enter, dethunk, etc. It moves
// some pointers around.

impl Engine {
    #[instrument(skip(self))]
    fn goto(&self, to: ApplicativeForm, label: &str) -> MResult<StepDone> {
        *self.state.code.borrow_mut() = to;
        Ok(StepDone::Again)
    }

    #[instrument(skip(self))]
    fn enter(&self, c: Continuation) {
        self.state.stack.borrow_mut().push(c);
    }

    #[instrument(skip(self))]
    fn push(&self, to: ApplicativeForm, c: Continuation, label: &str) -> MResult<StepDone> {
        // avoid generating extra `instrument` spans
        self.state.stack.borrow_mut().push(c);
        *self.state.code.borrow_mut() = to;
        Ok(StepDone::Again)
    }

    /// Read out the current expr, replacing it with `empty`
    /// it is an error to not put something back before the next step.
    fn take_code(&self) -> ApplicativeForm {
        let t = RefCell::new(ApplicativeForm::Ref(Ref::prim(Empty)));
        self.state.code.swap(&t);
        trace!("took out of code register: {}", t.borrow());
        t.into_inner()
    }

    #[instrument(skip(self))]
    fn leave(&self) -> Option<Continuation> {
        let c = self.state.stack.borrow_mut().pop();
        trace!("leaving {:?}", c);
        c
    }

    #[instrument(skip(self))]
    fn call(&self, e: ApplicativeForm, args: RefList, label: &str) -> MResult<StepDone> {
        *self.state.arg_storage.borrow_mut() = args;
        *self.state.code.borrow_mut() = e;
        Ok(StepDone::Again)
    }

    #[instrument(skip(self))]
    fn callfun(&self, head: Ref, arity: u64, mut args: RefList) -> MResult<StepDone> {
        use crate::graph::TaggedObjView::*;
        //assert!(head.)
        use std::cmp::Ordering;
        let provided_arity = args.len() as u64;

        // provided_arity is `n` from the paper, arity is `n`
        match arity.cmp(&provided_arity) {
            // compare the size of the argument lists. if they mismatch, handle it by either
            // applying args now or else saving them for later.
            Ordering::Equal => {
                // KNOWNCALL and also EXACT... do these need to be separate somehow?
                info!(
                    "here in knowncall, we have {:?} here in the head and arity {} from the fundef",
                    head, arity
                );
                let _ = self.call(ApplicativeForm::Ref(head), args, "EXACT")?;
            }
            Ordering::Less => {
                // we have more args than we need to apply head, take the ones it needs
                // n < m
                let rest = args
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .split_off(arity as usize); // TODO fixme: linked list pls
                self.enter(Apply(rest.into()));
                let _ = self.call(ApplicativeForm::Ref(head), args, "CALLK")?;
                // and when we're with it, apply its result to the remainder.
            }
            Ordering::Greater => {
                // n > m, we need more args before we can progress, suspend into a PAP
                let obj = self.state.heap.partially_apply(head, args);
                //info!("i have now constructed {} partials", self.partial_count.fetch_add(1, std::sync::Ordering::SeqCst));
                return self.goto(ApplicativeForm::Ref(obj), "PAP2");
            }
        }

        // alrighty now. we may have just installed a Prim token into code register,
        // and if that's the case then we actually need to pause briefly and force
        // the arguments to the function.

        let t = self.take_code();
        match t {
            ApplicativeForm::Ref(r) => match r.deref() {
                Builtin(p)
                    if p.needs_force()
                        && self.state.arg_storage.borrow().iter().any(Ref::needs_force) =>
                {
                    let mut args = smallvec![];
                    std::mem::swap(&mut args, &mut *self.state.arg_storage.borrow_mut());
                    self.push(
                        ApplicativeForm::Ref(args[0].clone()),
                        ForceArgs(ForceArgsState {
                            head: Ref::prim(p),
                            index_cur: 0,
                            args,
                        }),
                        "force args",
                    )
                }
                Builtin(p) => self.prim(p, None),
                _ => self.goto(t, "repair (not a primcall)"),
            },
            _ => self.goto(t, "repair (not a primcall)"),
        }
    }

    fn prim_fundef(&self, p: Primitive) -> FunDef {
        let (fd, cr) = match self.state.prim_fundefs.borrow().get(p as usize).cloned() {
            Some(Some((ref fd, _))) => return fd.clone(),
            _ => {
                let cell_root = self.state.heap.allocate(
                    RefTag::Extended,
                    crate::graph::ObjData {
                        extended: ManuallyDrop::new(crate::graph::ExtendedData::Blackhole),
                    },
                );
                let fd = FunDef {
                    body: Arc::new(ApplicativeForm::Ref(Ref::prim(p))),
                    arity: p.arity() as u64,
                };

                (fd, cell_root)
            }
        };
        self.state.prim_fundefs.borrow_mut()[p as usize] = Some((fd.clone(), cr));
        fd
    }
}

//#endregion

//#region Misc support types

/// Primitive structures the machine knows how to apply in a single step.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Primitive {
    Inc,
    Dec,
    Add,
    Mul,
    Div,
    Eq,
    Lt,
    Mod,
    Demod,
    Send,
    Neg,
    Ap,
    S,
    C,
    B,
    T,
    F,
    Pwr2,
    I,
    Cons,
    Car,
    Cdr,
    Nil,
    IsNil,
    /// the = symbol, parsed for commands
    Define,
    /// the VM uses this to represent "empty", eg the empty machine state is "evaluating empty"
    Empty,
    If0,
    Draw,
    Multidraw,
    // draw, checkerboard, multidraw, modulate list, send, interact, etc+
}

use Primitive::*;

//#region Primitive operation definitions

impl Engine {
    fn evaluate_prim(&self, prim: Primitive) -> MResult<ApplicativeForm> {
        use std::ops::Neg;

        // first off, let's just steal those args...
        // we shouldn't need to ever put them back.
        let mut args = smallvec![];
        std::mem::swap(&mut args, &mut self.state.arg_storage.borrow_mut());

        if args.len() != prim.arity() as usize {
            return err(ArgLenMismatch(prim, args.len(), args));
        }

        let evaled_op = (|| {
            // and do a case examination!
            let data: MResult<Ref> = match prim {
                Inc => self.map_num(args[0], |x| *x += 1),
                Dec => self.map_num(args[0], |x| *x -= 1),
                Add => {
                    let n2 = args[1].num()?;
                    self.map_num(args[0], |x| *x += &*n2)
                }
                Mul => {
                    let n2 = args[1].num()?;
                    self.map_num(args[0], |x| *x *= &*n2)
                }
                Div => {
                    let n2 = args[1].num()?;
                    self.map_num(args[0], |x| *x /= &*n2)
                }
                Eq => Ok(if args[0].num()? == args[1].num()? {
                    Ref::prim(T)
                } else {
                    Ref::prim(F)
                }),
                Lt => Ok(if args[0].num()? < args[1].num()? {
                    Ref::prim(T)
                } else {
                    Ref::prim(F)
                }),
                Neg => self.map_num(args[0], |x| *x = x.clone().neg()),
                Pwr2 => {
                    let mut res = None;
                    let newval = self.map_num(args[0], |x| match <u32 as std::convert::TryFrom<
                        &num::BigInt,
                    >>::try_from(&x)
                    {
                        Ok(exp) => {
                            *x = num::BigInt::from(2).pow(exp);
                            res = Some(Ok(()))
                        }
                        Err(_) => res = Some(err(LargeExponent)),
                    });
                    res.unwrap()?;
                    newval
                }
                Mod => todo!("mod"),
                Demod => todo!("demod"),
                Send => todo!("send"),
                Ap => {
                    // ap = ap b i
                    //    ap ap (ap b i) x0 x1 =
                    // ->          ap i (ap x0 x1)
                    // ->               ap x0 x1
                    if let [x0, x1] = args[..2] {
                        return Ok(self.state.heap.ea(
                            self.state
                                .heap
                                .ea(self.state.heap.aa(Ref::prim(B), Ref::prim(I)), x0),
                            x1,
                        ));
                    }
                    unreachable!()
                }
                S => {
                    // ap ap x0 x2 ap x1 x2
                    if let [x0, x1, x2] = args[..3] {
                        return Ok(self
                            .state
                            .heap
                            .ee(self.state.heap.aa(x0, x2), self.state.heap.aa(x1, x2)));
                    }
                    unreachable!()
                }
                C => {
                    // ap ap x0 x2 x1
                    if let [x0, x1, x2] = args[..3] {
                        return Ok(self.state.heap.ea(self.state.heap.aa(x0, x2), x1));
                    }
                    unreachable!()
                }
                B => {
                    // ap x0 ap x1 x2
                    if let [x0, x1, x2] = args[..3] {
                        return Ok(self.state.heap.ae(x0, self.state.heap.aa(x1, x2)));
                    }
                    unreachable!()
                }
                Nil => Ok(Ref::prim(T)),
                T => Ok(args[0]),
                F => Ok(args[1]),
                I => Ok(args[0]),
                Cons => {
                    if let [x0, x1] = args[..2] {
                        Ok(self
                            .state
                            .heap
                            .allocate(RefTag::Pair, crate::graph::ObjData { pair: (x0, x1) }))
                    } else {
                        unreachable!()
                    }
                }
                Car => return Ok(self.state.heap.aa(args[0], Ref::prim(T))),
                Cdr => return Ok(self.state.heap.aa(args[0], Ref::prim(F))),
                IsNil => Ok(if matches!(args[0].deref(), TaggedObjView::Builtin(Nil)) {
                    Ref::prim(T)
                } else {
                    Ref::prim(F)
                }),
                If0 => {
                    self.enter(KIf0(smallvec![args[1], args[2]]));
                    Ok(args[0].clone())
                }
                Empty => err(Mistake("cannot evaluate empty")),
                Multidraw | Draw => todo!("drawing"),
                Define => unreachable!("this token shouldn't have escaped parsing"),
            };
            data.map(ApplicativeForm::Ref)
                .map_err(|e| EngineError::new(PrimPanic(Box::new(e))))
        })();

        std::mem::swap(&mut args, &mut self.state.arg_storage.borrow_mut());

        evaled_op
    }
}

impl Primitive {
    fn arity(&self) -> u16 {
        use Primitive::*;
        match self {
            Empty => 0,
            I | IsNil | Inc | Dec | Mod | Demod | Send | Neg | Pwr2 | Nil | Car | Cdr => 1,
            Ap | Add | Mul | Div | Lt | Eq | T | F | Cons => 2,
            S | C | B | If0 => 3,
            Draw | Multidraw => todo!(),
            Define => unreachable!("toplevel only"),
        }
    }
    fn needs_force(&self) -> bool {
        use Primitive::*;
        match self {
            IsNil | Inc | Dec | Mod | Demod | Send | Neg | Pwr2 | Nil | Car | Cdr | Add | Mul
            | Div | Lt | Eq => true,
            Cons | Empty | If0 | S | I | Ap | C | B | T | F => false,
            Draw | Multidraw => todo!(),
            Define => unreachable!("toplevel only"),
        }
    }
}
//#endregion

//#endregion

// this could totally be a trait object but i didn't reach for that first for Reasons...
pub struct DataVisitor<Cons, Nil, Num> {
    pub visit_cons: Cons,
    pub visit_nil: Nil,
    pub visit_num: Num,
}

// The rest of the file is just helpers and nonsense. Peruse as needed.

/// utilities
impl Ref {
    fn needs_force(&self) -> bool {
        self.deref().needs_force()
    }

    fn is_value(&self) -> bool {
        self.deref().is_value()
    }
}

//#region Grab bag of trait implementations
impl Display for Continuation {
    fn fmt(&self, f: &mut Fmt) -> FR {
        match self {
            KIf0(l) => write!(f, "kif0 _ {}", l.iter().join_with(" ").to_string()),
            UpdThunk(_) => write!(f, "upd"),
            Apply(l) => write!(f, "apply _ ({})", l.iter().join_with(" ").to_string()),
            ForceList(ReducingTail, _) => f.write_str("forcing (other :: _)"),
            ForceList(ReducingHead(hd), _) => write!(f, "forcing (_ :: {})", hd),
            ForceArgs(st) => write!(f, "force {} {}", st.head, st.args.iter().join_with(" ")),
        }
    }
}
impl fmt::Debug for ApplicativeForm {
    fn fmt(&self, f: &mut Fmt) -> FR {
        match self {
            ApplicativeForm::Ref(a) => write!(f, "{:?}", a),
            ApplicativeForm::Apply(v, _, args) => write!(f, "{} {:?}", v, args),
        }
    }
}
impl Display for ApplicativeForm {
    fn fmt(&self, f: &mut Fmt) -> FR {
        let (v, args) = match self {
            ApplicativeForm::Ref(a) => return a.fmt(f),
            ApplicativeForm::Apply(v, _a, args) => (format!("{}", v), args),
        };
        // legitimately copied+pasted from above, been a while since i done that
        // put the aps back
        let mut s = VecDeque::new();
        s.push_back(v);
        for arg in args {
            s.push_front("ap ".into());
            s.push_back(format!(" {}", arg));
        }
        for s in s {
            f.write_str(&s)?;
        }
        Ok(())
    }
}
impl Display for Engine {
    fn fmt(&self, f: &mut Fmt) -> FR {
        write!(f, "{}", self.state)
    }
}

impl Display for State {
    fn fmt(&self, f: &mut Fmt) -> FR {
        write!(
            f,
            "{:?} , {}]",
            self.code.borrow(),
            self.stack
                .borrow()
                .iter()
                .map(|x| format!("{:?}", x))
                .rev()
                .join_with(" ; ")
                .to_string()
        )
        //x.iter().map(|x| format!("{:?}", x)) .rev() .join_with("\n\t> ")))
    }
}

impl Default for State {
    fn default() -> Self {
        Self::new()
    }
}
//#endregion

//type Level = u16;
//fn apply_substitution<Sig>(sigma_0: Sig)
//  where Sig : Fn(Level) ->

//#region Error types and such

#[derive(thiserror::Error, Debug)]
pub enum EngineErrorKind {
    #[error(
        "while {} expected something of type {:?} but found value {:?}",
        when,
        expected,
        found
    )]
    TypeMismatch {
        expected: Ty,
        found: Ref,
        when: &'static str,
    },
    #[error("cannot evaluate {} further", .0)]
    Stuck(ApplicativeForm),
    #[error("error while evaluating primitive: {}", .0)]
    PrimPanic(Box<EngineError>),
    #[error("if0 condition should be zero or one")]
    EIf0,
    #[error("tried to apply a number")]
    CalledNumber,
    #[error("exponent was too large to compute with")]
    LargeExponent,
    #[error("this was a mistake, {}", .0)]
    Mistake(&'static str),
    #[error("applied {:?} with {:?} args ({:?}) when it wants {}", .0, .1, .2, .0.arity())]
    ArgLenMismatch(Primitive, usize, RefList),
    #[error("parsing error: {}", .0)]
    Parsing(crate::parse::ParsingError),
}

use EngineErrorKind::*;

// this Ty type is only used for error reporting and such
#[derive(Debug, Clone)]
#[doc(hidden)]
pub enum Ty {
    Num,
    Ref,
    HeapObj,
    Prim,
    Sym,
    Callable,
}

#[derive(Debug, thiserror::Error)]
pub struct EngineError {
    source: EngineErrorKind,
    caller: &'static std::panic::Location<'static>,
    //code_context: ApplicativeForm,
    cont_context: Vec<Continuation>,
    //toplevel: ApplicativeForm,
}

impl From<crate::parse::ParsingError> for EngineError {
    #[track_caller]
    fn from(e: crate::parse::ParsingError) -> EngineError {
        EngineError::without_debug(Parsing(e))
    }
}

impl From<std::option::NoneError> for EngineError {
    #[track_caller]
    fn from(_: std::option::NoneError) -> EngineError {
        EngineError::new(Mistake("unwrapped none"))
    }
}
impl EngineError {
    #[track_caller]
    #[illicit::from_env(engine: &Rc<Engine>)]
    fn new(source: EngineErrorKind) -> EngineError {
        //let code_context = ApplicativeForm::clone(&engine.state.code.borrow());
        let cont_context = Vec::clone(&engine.state.stack.borrow());
        //let toplevel = ApplicativeForm::clone(&engine.state.code.borrow());

        EngineError {
            source,
            caller: std::panic::Location::caller(),
            //toplevel,
            //code_context,
            cont_context,
        }
    }
    #[track_caller]
    pub fn without_debug(source: EngineErrorKind) -> EngineError {
        EngineError {
            source,
            caller: std::panic::Location::caller(),
            //toplevel,
            //code_context,
            cont_context: vec![],
        }
    }
}

impl Display for EngineError {
    fn fmt(&self, f: &mut Fmt) -> FR {
        write!(
            f,
            r"
w~w~w~w~w~w~w~w~w~ yikes! ~w~w~w~w~w~w~w~w~w~w~w~w~w
|    {} caused at {}
|   
|    the control stack looked like this: {}
w~w~w~w~w~w~w~w~w~w~w~w~w~w~w~w~w~w~w~w~w~w~w~w~w~w
    ",
            self.source,
            self.caller,
            //self.code_context,
            self.cont_context
                .iter()
                .rev()
                .map(|x| format!("{:?}", x))
                .join_with("\n\t"),
            //self.toplevel
        )
    }
}

#[track_caller]
pub(crate) fn err<T>(source: EngineErrorKind) -> MResult<T> {
    // FIXME: handle gracefully the case where we cannot read out the state?
    Err(EngineError::new(source))
}

//#endregion
