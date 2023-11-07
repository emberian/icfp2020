#![allow(unreachable_code, dead_code, unused_variables)]

use alloc::sync::{Arc, Weak};
use core::alloc::{GlobalAlloc, Layout};
use core::cell::{Cell, RefCell, UnsafeCell};
use core::mem::transmute;
use core::ptr::NonNull;
use core::raw::TraitObject;
use core::sync::atomic::{
    AtomicBool, AtomicPtr, AtomicUsize,
    Ordering::{AcqRel, Acquire, Release},
};

use parking_lot::{Mutex, RwLock};
use thread_local::CachedThreadLocal;

use crate::bitmap::{Bitmap, Bitptr, Result::Failure, Result::Success};
use crate::segment::*;
use crate::trace::Trace;

use State::*;

pub const LOG2_MIN_OBJ_SIZE: usize = 3;
pub const LOG2_MAX_OBJ_SIZE: usize = 12;
pub const NUM_SUBHEAPS: usize = LOG2_MAX_OBJ_SIZE - LOG2_MIN_OBJ_SIZE;

// SAFETY: gc sync mechanisms ensure threadstate is only ever accessed by a
// single thread at a time: it's the one that has the thread local referencing
// it, or else the collector thread (which might be the same thread). given
// the *mut ThreadState in a heap registration, it should always be safe to
// dereference and access it.
#[derive(Debug)]
pub struct ThreadState<Hdr: 'static> {
    pub(crate) state: AtomicState,
    pub(crate) barrier: ObjList<'static, Hdr>,
    // FIXME: this should really be pinned?
    pub(crate) subheaps: UnsafeCell<[SubHeap; 3 + NUM_SUBHEAPS]>,
    // TODO: large allocation dedicated subheap
    /// CORRECTNESS: tmproot can only be modified during SYNC2 (root enumeration)
    pub(crate) tmproot: UnsafeCell<ObjList<'static, Hdr>>,
    pub(crate) heap: Weak<Heap<Hdr>>,
    /// Viewers: both heap registrations and gc roots count as viewers. why gc
    /// roots? because gc roots get put into this thread's root list. This is a
    /// refcount. FIXME: upgrade to Arc<ThreadState> instead of this inline
    /// refcount?
    pub(crate) viewers: AtomicUsize,
    pub(crate) roots: UnsafeCell<Vec<*mut u8>>,
    pub(crate) _pin: core::marker::PhantomPinned,
    //TODO: hookable root enumeration
    //pub scan_roots: UnsafeCell<Box<dyn FnMut()>>,
}

unsafe impl<Hdr: 'static> Send for ThreadState<Hdr> {}

static GC_CONTEXT: &str =
    "oof: ran gc methods on a thread that whose GC is uninitialized or deallocated; is heap packing/sending broken?";

static GC_SEGMENT: &str = "gc bumped a heap without an assigned a segment?";

/// Thread-specific methods.
impl<Hdr: 'static> ThreadState<Hdr> {
    // HOTPATH
    pub(crate) fn find_subheap(&self, size: usize) -> Option<&SubHeap> {
        // ok the paper mentions that "it determines H_i for about 93% of allocation
        // requests by 2 comparisons". they didn't mention details and don't mention
        // source availability, so let's see what we can do for now...
        // first off, the four cases...
        let subheap_idx = if size <= 16 {
            if size == 16 {
                4
            } else {
                // size == 8
                3
            }
        } else if size == 32 {
            5
        } else {
            // decision diagram bottoms out here i guess?
            let res = crate::segment::log2(size);
            if res >= crate::heap::LOG2_MAX_OBJ_SIZE {
                return None;
            }
            res
        };

        // ok after implementing that i realized this is also just segment::log2?
        // FIXME: benchmark this lol now that it's written it may as well stay bcuz layz

        // SAFETY: subheaps is ours.
        unsafe { Some(&(*self.subheaps.get())[subheap_idx]) }
    }

    /// Write barrier. Notify the GC that ptr, and possibly things reachable by it,
    /// is about to be set to `val`. If the collector thread is running and in the
    /// mark phase, trace the value immediately.
    ///
    /// # Safety
    ///
    /// This is safe as long as `ptr` is the same as `val`.
    pub unsafe fn write_barrier(&self, ptr: usize, val: &(dyn Trace + Sync)) {
        match self.state.load(Acquire) {
            S1S1 | S2S1 | S2S2 => {
                self.heap.upgrade().expect(GC_CONTEXT).remember(ptr);
            }
            Mark => {
                let heap = self.heap.upgrade().expect(GC_CONTEXT);
                heap.remember(ptr);
                // TODO: todo!("lookup traceptr from table. if it's different from val, update it. if there isn't space in the trace table, panic");
                val.visit(
                    // SAFETY: depends on the callee transmuting back appropriately
                    core::mem::transmute::<&Heap<Hdr>, &Heap<()>>(&*heap),
                    &move |&ptr| drop(heap.remember(ptr)),
                );
            }
            _ => {}
        }
    }

    /// Take a snapshot of the current thread's segments on all subheaps
    fn snapshot(&self) {
        crate::instrument("subheap snapshotting", || unsafe {
            // SAFETY: we are the only thread that uses the allocptr_snap or subheap
            for subheap in (&mut *self.subheaps.get()).iter_mut() {
                subheap
                    .allocptr()
                    .copy_into(&mut *subheap.allocptr_snap.get());
            }
        });
    }

    /// Retrieve the next segment to use locally for the given subheap. Err on OOM.
    ///
    /// SAFETY: assumes `sh` is initialized
    pub(crate) fn get_segment(&self, sh: &SubHeap) -> crate::bitmap::Result {
        // toplevel gc entry from mutators?
        if matches!(self.state.load(Acquire), S2S1 | S1S1) {
            self.snapshot()
        }
        loop {
            // FIXME: bound loop
            if sh.is_full() {
                sh.replace_filled_segment::<Hdr>();
                // paper says a good heuristic for when to gc is when we've filled a segment. ok.
                if let Some(h) = self.heap.upgrade() {
                    h.maybe_gc()
                }
            }
        }
    }

    fn handshake(&self) {
        if let Some(h) = self.heap.upgrade() {
            h.handshake.increment();
        }
    }

    /// Check in with the garbage collector and see if the global phase has changed
    /// yet.
    pub fn check_gc(&self) {
        match self.state.load(Acquire) {
            S1A => {
                self.handshake();
                self.state.store(S1S1, Release)
            }
            S2S1 => {
                self.snapshot();

                if let Some(heap) = self.heap.upgrade() {
                    // swap our new roots into the collector's list
                    // SAFETY: the gc doesn't inspect tmproot if a thread is active
                    let tmproot =
                        unsafe { core::ptr::replace(self.tmproot.get(), ObjList::empty()) };

                    if let Some(tmproot) = tmproot.0 {
                        // SAFETY: roots has a bunk type, otherwise this would be a plain insert.
                        // As for the NonNull, UnsafeCell::get will never return null
                        unsafe {
                            ObjList::cast_insert(
                                Packed::from_pointer_and_bits(&heap.roots, 0),
                                tmproot,
                            );
                        }
                    }
                }

                self.handshake();
                self.state.store(S2S2, Release);
            }
            _ => {}
        }
    }
}

/// The states a thread can be in, as a combination of the global state and the
/// local state. See the paper for more, or `Heap::gc` for what the states mean.
#[atomic_enum::atomic_enum]
pub(crate) enum State {
    Async,
    S1A,
    S1S1,
    S2S1,
    S2S2,
    Mark,
}

/// The block allocator we use to get new segment blocks
pub(crate) struct BlockAlloc(pub(crate) Mutex<Box<dyn GlobalAlloc + Send>>);
impl core::fmt::Debug for BlockAlloc {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.write_str("<block allocator>")
    }
}

/// A garbage-collected heap. See the module-level docs for more information
/// about the garbage collection algorithm.
#[derive(Debug)]
pub struct Heap<Hdr: 'static> {
    pub(crate) block_alloc: BlockAlloc,
    // if a mask is 32KiB (2^15), this will be 2^15-1 ie 0xEF
    pub(crate) segment_mask: usize,
    // the collector gets registered as the owner for the local (getting very
    // fast access, which aids in faster collector times), and also happens
    // to be the only thread that cares about taking the write lock
    pub(crate) initstate: AtomicState,
    pub(crate) cur_thread: RwLock<CachedThreadLocal<ThreadState<Hdr>>>,
    pub(crate) roots: ObjHdr<()>,
    pub(crate) barrier: ObjHdr<()>,
    pub(crate) free: ObjHdr<()>,
    pub(crate) subheap_roots: UnsafeCell<[SubHeapRoots; 3 + NUM_SUBHEAPS]>,
    pub(crate) handshake: crate::handshake::Handshake,
    // the first four entries in every segment's trace table are these
    pub(crate) global_trace: [*mut (); 4],
}

#[derive(Debug)]
pub(crate) struct SubHeapRoots {
    filled: ObjHdr<()>,
    active: ObjHdr<()>,
    do_not_extend: Arc<AtomicBool>,
    used_slots: Arc<AtomicUsize>,
    total_slots: Arc<AtomicUsize>,
}
impl Default for SubHeapRoots {
    fn default() -> SubHeapRoots {
        SubHeapRoots {
            filled: (ObjectHeader::new(())),
            active: (ObjectHeader::new(())),
            do_not_extend: Arc::new(false.into()),
            used_slots: Arc::new(0.into()),
            total_slots: Arc::new(0.into()),
        }
    }
}
impl<Hdr: 'static> Heap<Hdr> {
    /// Allocate and initialize a new, empty segment for a given subheap and object layout.
    pub(crate) fn new_segment(
        &self,
        layout: Layout,
        sh: &SubHeap,
    ) -> Option<ObjListRef<'static, Segment>> {
        let alloc = self.block_alloc.0.lock();
        let newseg = unsafe {
            alloc.alloc(
                Layout::array::<u8>(self.segment_mask + 1)
                    .expect(GC_ARITH)
                    .align_to(self.segment_mask + 1)
                    .expect(GC_ARITH),
            )
        } as *mut ObjHdr<Segment>;
        let seg = Segment {
            containing_subheap: Cell::new(NonNull::from(sh)),
            trace: UnsafeCell::new(Bitmap::default()),
            objcount: Cell::new(0),
            layout: Cell::new(SegmentLayout::new::<()>(layout, self.segment_mask + 1)),
            trace_count: Cell::new(0),
            trace_tables: [core::ptr::null_mut(); 8],
        };
        unsafe {
            (*newseg).data.write(seg);
            core::ptr::write(
                &mut (*newseg).list_link,
                Cell::new(Packed(newseg as *mut (), core::marker::PhantomData)),
            );
        }
        // fully initialized now!
        Some(Packed::from_pointer_and_bits(unsafe { &*newseg }, 0))
    }

    // Run some heuristics to determine to run a GC
    pub(crate) fn maybe_gc(&self) {
        // TODO: check if there's an external collector thread, and then do nothing?
        // in the meantime, look at me! i'm the collector now!
        self.gc();
    }

    /// SAFETY: if this isn't a pointer to a gc managed object, we're going to be
    /// very sad.
    // COLLECTOR WARMPATH
    pub unsafe fn segment_and_idx(&self, ptr: NonNull<u8>) -> (*mut Segment, u32) {
        let segptr = (ptr.as_ptr() as usize & self.segment_mask) as *mut Segment;
        let objsz = (*segptr).layout.get().objsize; // this is 2^i
        let segment_offset = (ptr.as_ptr() as usize).wrapping_sub(segptr as usize);
        let scaled_index = segment_offset.wrapping_sub((*segptr).layout.get().objarr_off as usize);
        let index = scaled_index >> (*segptr).layout.get().objsize_log2;
        (segptr, index as u32)
    }

    unsafe fn remember(&self, ptr: usize) -> NonNull<ObjHdr<Hdr>> {
        // SAFETY: if null or a non-gc pointer got in this list, what happened??
        // TODO: PERF: hitting that refcount for every pointer is pretty painful
        let (seg, idx) = self.segment_and_idx(NonNull::new_unchecked(ptr as *mut _));
        let ptr = (*seg).header_from_index::<Hdr>(idx);
        ObjList::cast_insert(
            Packed::from_pointer_and_bits(&self.barrier, 0),
            Packed::from_pointer_and_bits(ptr.as_ref(), ptr.as_ref().list_link_bits()),
        );
        ptr
    }

    // the actual collection algorithm.
    // this can run on its own thread if it wants, but also any of the mutators
    // can just become the collector if they decide to call this.
    pub(crate) fn gc(&self) {
        // SAFETY: the thread states live forever, so don't worry too much about
        // it.
        let me_thread = unsafe {
            let thr = self.cur_thread.read();
            transmute::<&ThreadState<Hdr>, &ThreadState<Hdr>>(thr.get().expect(GC_CONTEXT))
        };
        // alright, it's time to stop letting new threads into the pool.
        // this write lock could be removed with some cleverness i feel?
        // it doesn't seem very worth it. this rwlock is pretty cheap.
        let mut threadlock = self.cur_thread.write();
        self.handshake
            .set_expected_count(threadlock.iter_mut().len());

        // NOTE: this also means no other thread can borrow a copy of its thread
        // state now! it's already running _right now_ if it ever is going to be
        // until this cycle ends the sync phases. this is a departure from the
        // paper: they only prevent threads from joining until SYNC2 starts.

        // end the ASYNC phase: it's time to pay attention to me, and they can start
        // by snapshotting their current segments
        for thread in &mut *threadlock {
            if let Async = thread.state.load(Acquire) {
                thread.state.store(S1A, Release);
                if thread.viewers.load(Acquire) == 0 {
                    thread.state.store(S1S1, Release);
                }
            } else {
                unreachable!("desync in phase ASYNC")
            }
        }

        // don't need to worry about running concurrently with the gc because i am
        // the gc right now.
        me_thread.check_gc();
        self.handshake.wait();

        // the "C" set from the paper.
        let filled_c = ObjList::empty();
        // SAFETY: safe to dereference subheap/collecting roots: we hold the
        // collector lock!
        for sh in unsafe { &mut *self.subheap_roots.get() } {
            // swap out all the filled segment lists for the empty list.
            filled_c.push(
                (sh.filled.list_link().swap(core::ptr::null_mut(), AcqRel) as *mut ObjHdr<Segment>)
                    .into(),
            );
        }

        // end the SYNC1 phase: all segments have been snapshotted, request root
        // sets from running threads, or just snag them ourselves if the thread
        // isn't running.

        for thread in &mut *threadlock {
            if let S1S1 = thread.state.load(Acquire) {
                thread.state.store(S2S1, Release);
                if thread.viewers.load(Acquire) == 0 {
                    thread.check_gc();
                }
            } else {
                unreachable!("desync in phase SYNC1")
            }
        }

        me_thread.check_gc();
        self.handshake.wait();

        for thread in &mut *threadlock {
            if let S2S2 = thread.state.load(Acquire) {
                thread.state.store(Mark, Release);
            } else {
                unreachable!("desync in phase SYNC2")
            }
        }

        // drop the threadlock, allowing Heap::start to proceed
        drop(threadlock);

        for seg in filled_c.iter() {
            let mut seg = NonNull::new(&seg.data as *const _ as *mut Segment).expect(GC_SEGMENT);
            // SAFETY: we have ownership over these segments
            // TODO: ... although the GC mutates through a concurrent &...
            // that's fine though afaict.
            let seg = unsafe { seg.as_mut() };
            // NOTE: paper says here "saves all the allocation pointers" but i put
            // allocptr into threadstate instead of the segment, as only the thread
            // needs it. presence in this list implies the allocptr points to the end
            // anyway, so i'm not sure what the point is?
            unsafe {
                // SAFETY: only gc touches trace
                // TODO: can we ditch the alive bitmap in subheap to use this?
                if let Some(bm) = seg.trace.get().as_mut() {
                    bm.clear()
                }
            }
        }

        // trace while there's still things in the barrier
        let mut objl = ObjList(Some(Packed::from_pointer_and_bits(&self.roots, 0)));
        loop {
            // SAFETY: UnsafeCell::get never returns null
            let mark_and_push = |ptr| {
                let mut bitptr = [Bitptr::default(); 16]; // TODO: FIXME: stop hardcoding 16
                let (seg, idx) =
                // SAFETY: if null or a non-gc pointer got in this list, what happened??
                unsafe { self.segment_and_idx(NonNull::new_unchecked(ptr)) };
                // SAFETY: collector owns the trace bitmap
                let bm = unsafe { (*seg).trace.get().as_mut() }.expect(GC_CONTEXT);
                if !bm.contains(idx) {
                    bitptr[0] = Bitptr::from_index(idx);
                    bm.set(&mut bitptr, 0);
                    // SAFETY: segment deref continues to be safe. nobody touches objcount but us.
                    unsafe {
                        (*seg).objcount.update(|x| x + 1);
                    }
                    objl.push(AtomicPtr::new(ptr as *mut _));
                }
                (seg, idx)
            };
            while let Some(root) = objl.remove() {
                let (seg, idx) = mark_and_push(&*root as *const _ as *mut u8);
                let traceable = unsafe {
                    transmute::<TraitObject, &dyn Trace>(TraitObject {
                        data: &root.data as *const _ as *mut (),
                        vtable: (*seg).trace_tables[(*seg)
                            .header_from_index::<Hdr>(idx)
                            .as_ref()
                            .list_link_bits()],
                    })
                };
                // SAFETY: haha this is totally going to race with a mutator, and
                // our vtable is going to be out of date if the mutator changed the
                // trace implementation out from under us.
                // TODO: make this safe.
                unsafe {
                    traceable.visit(
                        core::mem::transmute::<&Heap<Hdr>, &Heap<()>>(self),
                        &|ptr_ref: &usize| {
                            mark_and_push(*ptr_ref as *mut _);
                        },
                    );
                }
            }
            // SAFETY: our own barrier list is always fine to access, although note
            // that it's getting concurrently mutated!
            let res = self
                .barrier
                .list_link()
                .swap(core::ptr::null_mut(), Acquire);

            if !res.is_null() {
                objl = ObjList(Some(Packed::from_pointer_and_bits(unsafe { &*res }, 0)));
            } else {
                break;
            }
        }

        let mut threadlock = self.cur_thread.write();

        for thread in &mut *threadlock {
            if let S2S2 = thread.state.load(Acquire) {
                thread.state.store(Async, Release);
            } else {
                unreachable!("desync in phase MARK")
            }
        }

        for segment in filled_c.iter() {
            use core::cmp::Ordering::*;
            // SAFETY: everywhere below with a segment.data.assume_init_ref is gucci,
            // it's always init'd in this crate.
            let objcount = unsafe { segment.data.assume_init_ref() }.objcount.get();
            match objcount.cmp(
                &(unsafe { segment.data.assume_init_ref() }
                    .layout
                    .get()
                    .maxobj as usize),
            ) {
                Less => {
                    if objcount != 0 {
                        // still in use, what heap should this go into?
                        let subheap = &unsafe { &*self.subheap_roots.get() }[unsafe {
                            segment.data.assume_init_ref()
                        }
                        .layout
                        .get()
                        .objsize_log2
                            as usize];
                        // SAFETY: we own the subheat roots.
                        unsafe {
                            ObjList::cast_insert(
                                Packed::from_pointer_and_bits(&subheap.active, 0),
                                segment,
                            );
                        }
                    } else {
                        // completely unused segment! let's send this into the freelist.
                        // SAFETY: deref free is OK.
                        // TODO: decide to return this to the block allocator?
                        unsafe {
                            ObjList::cast_insert(
                                Packed::from_pointer_and_bits(&self.free, 0),
                                segment,
                            );
                        }
                    }
                }
                Equal => {
                    // this segment is still filled!
                    let subheap = unsafe {
                        &(&*self.subheap_roots.get())
                            [segment.data.assume_init_ref().layout.get().objsize_log2 as usize]
                    };
                    // SAFETY: we own the subheat roots.
                    unsafe {
                        ObjList::cast_insert(
                            Packed::from_pointer_and_bits(&subheap.filled, 0),
                            segment,
                        );
                    }
                }
                Greater => unreachable!(
                    "the gc thinks there are more objects in this segment than can possibly fit"
                ),
            }
        }
    }
}

#[derive(Debug)]
pub(crate) struct AllocPtr {
    pub(crate) cursor: Vec<crate::bitmap::Bitptr>,
    pub(crate) active_segment: Option<ObjListRef<'static, Segment>>,
    pub(crate) next_object: Option<NonNull<u8>>,
}
impl Default for AllocPtr {
    fn default() -> Self {
        AllocPtr {
            cursor: vec![],
            active_segment: None,
            next_object: None,
        }
    }
}
impl AllocPtr {
    pub(crate) fn copy_into(&self, other: &mut AllocPtr) {
        other.cursor.copy_from_slice(&self.cursor);
        other.active_segment = self.active_segment;
        other.next_object = self.next_object;
    }
}

#[derive(Debug, Default)]
pub(crate) struct SubHeap {
    args: SubHeapArgs,
    pub(crate) allocptr: RefCell<AllocPtr>,
    allocptr_snap: UnsafeCell<AllocPtr>,
    current_segment: Cell<Option<ObjListRef<'static, Segment>>>,
    alive: Bitmap,
    /// all subheaps of a given size share the following.
    free: ObjList<'static, Segment>,
    filled: ObjList<'static, Segment>,
    active: ObjList<'static, Segment>,
    do_not_extend: Arc<AtomicBool>,
    used_slots: Arc<AtomicUsize>,
    total_slots: Arc<AtomicUsize>,
}

#[derive(Debug, Default)]
pub struct SubHeapArgs {
    pub object_size: usize,
    pub segment_size: usize,
}

impl SubHeap {
    fn is_full(&self) -> bool {
        self.used_slots.load(Acquire) == self.total_slots.load(Acquire)
    }

    /// Replace the segment this subheap is allocating out of.
    ///
    /// This first consults the list of active blocks (those that are partially
    /// filled, given back to us by the GC after marking unreachable objects
    /// free) before checking the list of free (empty) segments. Otherwise, fail.
    /// Failure of this method is pretty common: it is a signal that we need to
    /// either run the GC or allocate a new segment for this subheap size.
    pub(crate) fn replace_filled_segment<Hdr: 'static>(&self) -> crate::bitmap::Result {
        // Check active for anything
        let mut seg = Some(match self.active.remove() {
            Some(seg) => seg,
            None => match self.free.remove() {
                // Ok, maybe free?
                Some(seg) => seg,
                None => return Failure, // our caller should consider calling gc and trying again.
            },
        });
        self.current_segment.swap(Cell::from_mut(&mut seg));
        let oldlayout = unsafe {
            self.current_segment
                .get()
                .expect(GC_CONTEXT)
                .data
                .assume_init_ref()
        }
        .layout
        .get();
        let oldseg = self.set_segment::<Hdr>(
            Layout::from_size_align(oldlayout.objsize as usize, oldlayout.objsize_log2 as usize)
                .expect(GC_ARITH),
            seg.expect("we just made it, it has to be some"),
        );
        self.filled
            .insert(oldseg.expect("we just filled it, it has to be some"));
        Success
    }

    pub(crate) fn set_segment<Hdr: 'static>(
        &self,
        layout: Layout,
        seg: ObjListRef<'static, Segment>,
    ) -> Option<ObjListRef<Segment>> {
        unsafe {
            seg.data
                .assume_init_ref()
                .containing_subheap
                .set(NonNull::new_unchecked(self as *const _ as *mut _));
            seg.data
                .assume_init_ref()
                .layout
                .set(SegmentLayout::new::<Hdr>(layout, self.args.segment_size));
            self.current_segment
                .replace(Some(Packed::from_pointer_and_bits(
                    transmute::<&ObjHdr<Segment>, &'static ObjHdr<Segment>>(&*seg),
                    0,
                )))
        }
    }

    // HOTPATH
    /// Move the allocptr to point to the next free object.
    ///
    /// SAFETY: precondition: this subheap already has a valid segment assigned
    /// SAFETY: only this thread can be mutating this subheap!
    pub(crate) unsafe fn bump(&self) -> crate::bitmap::Result {
        // TODO: is this actually safe? i am worried about these &mut...
        if let Failure = self.alive.next_not_contained(&mut self.allocptr().cursor) {
            return Failure;
        }
        self.allocptr().next_object = Some(
            self.current_segment
                .get()
                .expect(GC_SEGMENT)
                .data
                .assume_init_ref()
                .address_from_index(self.allocptr().cursor[0].to_index()),
        );
        Success
    }

    pub(crate) fn allocptr(&self) -> core::cell::RefMut<AllocPtr> {
        self.allocptr.borrow_mut()
    }
}
