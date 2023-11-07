//! Raw allocation blocks.
//!

use core::alloc::Layout;
use core::cell::{Cell, UnsafeCell};
use core::mem::{size_of, transmute, MaybeUninit};
use core::ptr::NonNull;

use core::sync::atomic::{
    AtomicPtr,
    Ordering::{AcqRel, Acquire},
};

use crate::bitmap::Bitmap;
use crate::heap::SubHeap;

pub(crate) static GC_ARITH: &str =
    "out of memory: arithmetic overflow during size/index calculation";

//#region Object headers on the heap, and the lists composed of them

/// Wrap a `T`, allowing it to be inserted into gc lists.
#[derive(Debug)]
pub struct ObjectHeader<T: 'static> {
    // note: the bottom three bits are actually an index into the trace tables?
    pub(crate) list_link: Cell<Packed<'static, ObjHdr<T>>>,
    pub data: MaybeUninit<T>,
}

pub type ObjHdr<T> = ObjectHeader<T>;

impl<T> ObjectHeader<T> {
    #[inline(always)] // i know it's a smell but look at it's, it's just a transmute!
    pub(crate) fn list_link(&self) -> &AtomicPtr<ObjHdr<T>> {
        unsafe { &*(&self.list_link.get().0 as *const *mut _ as *const _) }
    }
    pub(crate) fn load_next(&self) -> Option<NonNull<ObjHdr<T>>> {
        NonNull::new(&*self.list_link.get() as *const _ as *mut _)
    }
    pub(crate) fn list_link_bits(&self) -> usize {
        self.list_link.get().packed_bits()
    }
    pub(crate) fn new(data: T) -> ObjectHeader<T> {
        ObjectHeader {
            list_link: Cell::new(Packed(core::ptr::null_mut(), core::marker::PhantomData)),
            data: MaybeUninit::new(data),
        }
    }
}

// note: no drop! we don't care :) the lifetime is out of our hands.
#[derive(Debug)]
pub(crate) struct ObjList<'a, Hdr: 'static>(pub(crate) Option<ObjListRef<'a, Hdr>>);

impl<Hdr: 'static> Default for ObjList<'_, Hdr> {
    fn default() -> ObjList<'static, Hdr> {
        ObjList(None)
    }
}

pub(crate) type ObjListRef<'a, Hdr> = Packed<'a, ObjHdr<Hdr>>;

pub(crate) struct ObjListIter<'a, Hdr: 'static>(Option<ObjListRef<'a, Hdr>>);
impl<'a, Hdr: 'static> Iterator for ObjListIter<'a, Hdr> {
    type Item = ObjListRef<'a, Hdr>;
    fn next(&mut self) -> Option<ObjListRef<'a, Hdr>> {
        match &self.0 {
            None => None,
            Some(this) => {
                // SAFETY: `this` is valid for the lifetime of the heap.
                let next = this.list_link.get();
                core::mem::replace(&mut self.0, Some(next))
            }
        }
    }
}

impl<'a, Hdr: 'static> ObjList<'a, Hdr> {
    /// `{self == root -> a} ObjList::cast_insert(root, other) {self == root -> other -> a}`
    pub unsafe fn cast_insert<WhoCares>(root: ObjListRef<Hdr>, other: ObjListRef<WhoCares>) {
        ObjList(Some(root)).insert(transmute::<ObjListRef<WhoCares>, ObjListRef<Hdr>>(other))
    }

    pub fn iter(&self) -> ObjListIter<Hdr> {
        match self.0 {
            None => ObjListIter(None),
            Some(ptr) => ObjListIter(Some(ptr.list_link.get())),
        }
    }

    /// `{self == other -> tail} o = self.remove() {o == other && self -> tail}`
    pub fn remove(&self) -> Option<Packed<'a, ObjHdr<Hdr>>> {
        if let Some(slf) = self.0 {
            // SAFETY: lots of dereferencing of things that this list has
            // the same lifetime as. this tailptr is a packed under the
            // hood, so be careful with it.
            loop {
                let otherptr = slf.load_next()?;
                let otherpacked = slf.list_link.get();
                let packedotherptr = slf.list_link().load(Acquire);
                unsafe {
                    let packedtailptr = otherptr.as_ref().list_link().load(Acquire);
                    // {self == other -> tail}
                    if slf
                        .list_link()
                        .compare_and_swap(packedotherptr, packedtailptr, AcqRel)
                        != packedotherptr
                    {
                        continue;
                    }
                    return Some(otherpacked);
                }
            }
            // {self == slf ->  }
        }
        None
    }

    pub fn push(&self, other: AtomicPtr<ObjHdr<Hdr>>) {
        self.insert(Packed::from_pointer_and_bits(
            unsafe { &*other.load(Acquire) },
            1,
        ));
    }

    /// # Contract
    ///
    /// ```text
    /// {self == Some(tail)} self.insert(other) {self == Some(other -> tail) }
    /// {self == None} self.insert(other) {self == Some(other)}
    /// ```
    pub(crate) fn insert(&self, other: ObjListRef<Hdr>) {
        // SAFETY: assuming the gc doesn't drop blocks while they still have any
        // tracked objects, which is the core correctness property of the gc, these
        // pointers are always going to be live and valid etc.
        // CORRECTNESS: the atomics look like they make sense to me idk
        match self.0 {
            None => {
                // {self == nil}
                //self.0 = Some(other);
                // {self -> other}
                panic!("figure out if this needs to be atomic or not")
                // in the interim, we never call insert on an empty objlist.
            }
            Some(list_top) => {
                loop {
                    let packedtail = list_top.list_link().load(Acquire);
                    // {self -> tail}
                    // {other -> oldtail}
                    let _packedoldtail = other.list_link().swap(packedtail, AcqRel);
                    // {other -> tail}
                    if list_top.list_link().compare_and_swap(
                        packedtail,
                        other.list_link().load(Acquire),
                        AcqRel,
                    ) == packedtail
                    {
                        // loop post: {self -> other -> tail}
                        break;
                    }
                    // loop invariant: {}
                }
            }
        }
        // {self -> tail} self.insert(other) {self -> other -> tail}`
        // {self == None} self.insert(other) {self == other}
    }

    pub fn empty() -> Self {
        Self(None)
    }
}

//#endregion

/// Layout of a a heap block tracked by a segment.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct SegmentLayout {
    /// Offset from block start to object header array
    pub objhdrs_off: u32,
    /// Offset from block start to object payload array
    pub objarr_off: u32,
    /// Size of each object payload in bytes
    pub objsize: u32,
    /// Log2 of objsize
    pub objsize_log2: u32,
    /// Max number of objects this segment can hold
    pub maxobj: u32,
}

pub(crate) fn log2(x: usize) -> usize {
    size_of::<usize>()
        .wrapping_mul(8)
        .wrapping_sub(1)
        .wrapping_sub(x.leading_zeros() as usize)
}

// HOTPATH
#[inline]
#[track_caller]
pub(crate) fn roundup(mut x: usize) -> usize {
    if x <= 1 {
        1 // no free zero sized allocations, sadly, although we need space for their vtables anyway.
    } else {
        x -= 1;
        //println!("log2({}) = {}", x, log2(x));
        1 << log2(x)
    }
}

impl SegmentLayout {
    /// Compute the important details about the layout of a block
    pub fn new<Hdr: 'static>(obj: Layout, segment_len_bytes: usize) -> SegmentLayout {
        // we want to treat an object pointer as an aligned *mut [u64] at times,
        // make sure this is compatible with that.
        let obj = obj.align_to(8).expect(GC_ARITH);
        // additionally, we round all allocations up to the nearest power of 2.
        let obj = obj
            .align_to(roundup(obj.size()))
            .expect(GC_ARITH)
            .pad_to_align();

        // let's guess and see if the padding between [Header; N] and [Object; N]
        // is the same as Header and Object...

        let (est_prelayout, est_padding) = Layout::new::<ObjectHeader<Hdr>>()
            .extend(obj)
            .expect(GC_ARITH);

        let estimated_objects_available = (segment_len_bytes - size_of::<Segment>() - est_padding)
            / (obj.size() + size_of::<ObjectHeader<Hdr>>());

        let header_layout = Layout::new::<Segment>();

        let objhdrs =
            Layout::array::<ObjectHeader<Hdr>>(estimated_objects_available).expect(GC_ARITH);
        let (objarr, _) = obj.repeat(estimated_objects_available).expect(GC_ARITH);

        let (with_hdrs, objhdrs_off) = header_layout.extend(objhdrs).expect(GC_ARITH);
        let (prefinal_layout, objarr_off) = with_hdrs.extend(objarr).expect(GC_ARITH);

        let final_size = prefinal_layout.pad_to_align().size();

        let layout = SegmentLayout {
            objhdrs_off: objhdrs_off as u32,
            objarr_off: objarr_off as u32,
            objsize: obj.size() as u32,
            objsize_log2: log2(obj.size()) as u32,
            maxobj: estimated_objects_available as u32,
        };

        assert!(
            final_size <= segment_len_bytes,
            "whoa, incinerator has an obscure logic error and overflowed a block! not good! final size was {}, which is bigger than the segment size of {}. the layout we computed was {:?} and our input was {:?}", final_size, segment_len_bytes, layout, obj
        );

        debug_assert!( segment_len_bytes - final_size >= est_prelayout.pad_to_align().size(),
          "incinerator just wasted at least 1 potential object slot with its separated headers! computed {:?} from {:?} in a segment of size {}. i think there's space for {} in the naive layout, but the computed layout has {}", layout, obj, segment_len_bytes, segment_len_bytes-final_size/est_prelayout.pad_to_align().size(), estimated_objects_available);

        layout
    }
}

#[derive(Debug)]
pub struct Segment {
    // SAFETY: FIXME: this only works because we never deallocate subheaps
    pub(crate) containing_subheap: Cell<NonNull<SubHeap>>,
    pub trace: UnsafeCell<Bitmap>,
    pub objcount: Cell<usize>,
    pub layout: Cell<SegmentLayout>,
    pub trace_count: Cell<u32>,
    pub trace_tables: [*mut (); 8],
}

impl Segment {
    /// Return the object pointer for a given index into this segment.
    // HOTPATH
    #[inline]
    pub unsafe fn address_from_index(&self, index: u32) -> NonNull<u8> {
        NonNull::new_unchecked(
            (self as *const _ as usize)
                .wrapping_add(self.layout.get().objarr_off as usize)
                .wrapping_add((index as usize).wrapping_mul(self.layout.get().objsize as usize))
                as *mut u8,
        )
    }

    /// Return the header pointer for the ojbect at the given index in this
    /// segment.
    ///
    /// Will happily give an out-of-bounds pointer!
    // COLLECTOR WARMPATH
    #[inline]
    pub unsafe fn header_from_index<Hdr: 'static>(&self, index: u32) -> NonNull<ObjHdr<Hdr>> {
        NonNull::new_unchecked(
            ((self as *const _ as usize).wrapping_add(self.layout.get().objhdrs_off as usize)
                as *mut ObjHdr<Hdr>)
                .offset(index as isize),
        )
    }
}

/// A pointer with bits packed into the lower 3 bits. It's Deref, so.
#[derive(Debug)]
pub struct Packed<'a, T>(
    pub(crate) *mut (),
    pub(crate) core::marker::PhantomData<&'a T>,
);
impl<T> Copy for Packed<'_, T> {}
impl<T> Clone for Packed<'_, T> {
    fn clone(&self) -> Self {
        Packed(self.0, self.1)
    }
}
impl<T> Packed<'_, T> {
    /// Just the bits.
    pub(crate) fn packed_bits(&self) -> usize {
        self.0 as usize & 0b111
    }
    /// Pack 'em in
    pub(crate) fn from_pointer_and_bits(ptr: &T, bits: usize) -> Packed<T> {
        assert!(bits < 8);
        Packed(
            (ptr as *const T as usize | (bits & 0b111)) as *mut (),
            core::marker::PhantomData,
        )
    }
}
impl<T> core::ops::Deref for Packed<'_, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { transmute::<usize, &T>(self.0 as usize & !0b111) }
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use std::alloc::Layout;

    use std::sync::Arc;

    #[allow(dead_code)]
    pub enum FakeObj {
        Thunk(Arc<()>),
        Symbol(Arc<()>, Arc<()>),
        Partial(Vec<()>, usize, [u32; 4]),
        Pair(u8, u8),
    }

    /// Check that some layouts work the way we expect
    /// TODO: move this to runtime, during heap init. "layout self-test". in case a
    /// specific arch or something does weirds? idk.
    #[test]
    fn layout_examples() {
        let _lay1 = SegmentLayout::new::<()>(Layout::new::<u64>(), 512);
        let _lay2 = SegmentLayout::new::<()>(Layout::new::<u8>(), 512);
        let _lay3 = SegmentLayout::new::<()>(Layout::new::<FakeObj>(), 32 * 1024);
        let _lay4 = SegmentLayout::new::<FakeObj>(Layout::new::<u64>(), 32 * 1024);
        let _lay5 = SegmentLayout::new::<FakeObj>(Layout::new::<FakeObj>(), 32 * 1024);
        // TODO: actually look at this? although not overflowing is a good start.
    }
}
