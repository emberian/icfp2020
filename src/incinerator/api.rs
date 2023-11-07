use core::alloc::GlobalAlloc;
use core::alloc::Layout;
use core::cell::UnsafeCell;
use core::mem::transmute;
use core::mem::MaybeUninit;
use core::pin::Pin;
use core::ptr::NonNull;
use core::sync::atomic::Ordering::{AcqRel, Acquire};
use parking_lot::{Mutex, RwLock};
use thread_local::CachedThreadLocal;

use alloc::sync::Arc;

use crate::bitmap::Result::Failure;
use crate::heap::*;
use crate::segment::*;

pub struct GcRoot<Hdr: 'static, T: ?Sized> {
    _ptr: NonNull<T>,
    _owner: Arc<Heap<Hdr>>,
}

impl<Hdr, T: ?Sized> Drop for GcRoot<Hdr, T> {
    fn drop(&mut self) {}
}

/// Thread-local state for using a particular [`Heap`](./struct.Heap.html).
///
/// Through a registration, all heap functionality can be had. There can be
/// multiple registration for a particular heap on a single thread, and heap
/// registrations can be cloned. For as long as a thread is registered, it should
/// call at the _very least_
#[derive(Clone)]
pub struct HeapRegistration<Hdr: 'static> {
    // FIXME: Pin<Arc<ThreadState>> ? ThreadState isn't Send or Sync.
    pub state: NonNull<ThreadState<Hdr>>,
    // we must keep the heap alive so that our threadstate pointer remains valid
    pub heap: Pin<Arc<Heap<Hdr>>>,
}

impl<Hdr: 'static> HeapRegistration<Hdr> {
    /// Allocate new space for an object conforming to `layout`.
    ///
    /// This does not set up tracing for the resulting object. If it
    /// contains any pointers into this heap, they will not count and
    /// it will be very sad.
    pub fn alloc_raw(&self, layout: Layout) -> Option<NonNull<u8>> {
        // HOTPATH
        // FIXME: specify trace/finalize here?
        // FIXME: i'm probably botching alignment handling?
        // SAFETY: always safe to deref our local state
        let subheap = unsafe { self.state.as_ref() }
            .find_subheap(layout.align_to(8).expect("address arith error?").size())?;
        // SAFETY: we're the only owner of our allocptr
        unsafe {
            let res = subheap.allocptr().next_object;
            if let Failure = subheap.bump() {
                // SAFETY: always safe to deref our threadstate
                if let Failure = self.state.as_ref().get_segment(&subheap) {
                    // TODO: consider if this should return res and error out
                    // on the next alloc?
                    return None;
                }
            }
            res
        }
    }

    /// Run a garbage collection cycle using this thread as the collector.
    ///
    /// This informs all other running threads for this heap that it is time to
    /// scan their roots and tell us about them, and to enable the write
    /// barriers. A heap snapshot is taken and this thread starts tracing the
    /// object graph. Eventually it will complete and more memory will magically
    /// be available for the other threads (and ourself).
    pub fn gc(&self) {
        self.heap.gc();
    }

    /// Run a garbage collection cycle if the heuristics say we should.
    pub fn maybe_gc(&self) {
        self.heap.maybe_gc();
    }

    /// Check in to see if a collector thread needs our attention.
    pub fn check(&self) {
        // SAFETY: thread state always safe to deref
        unsafe { self.state.as_ref() }.check_gc();
    }

    /// Move `val` into the GC-managed heap.
    ///
    /// This will try and allocate a slot for a `T`. It will return `None` if
    /// there is no more memory: the GC is completely out of free slots for that
    /// size class, and our parent allocator isn't giving us new segments.
    ///
    /// # Safety
    ///
    /// This method is safe if you initialize the memory before this thread's
    /// next call to `alloc`.
    ///
    /// The object needs to be initialized before the next call to `alloc` on
    /// this thread with an object in the same size class as `T`. Otherwise, the
    /// garbage collector will try and call `Trace::visit` on uninitialized data!
    /// Very bad!
    pub unsafe fn alloc<T: crate::Trace + Sync>(
        &self,
        val: T,
    ) -> Option<(NonNull<T>, NonNull<MaybeUninit<Hdr>>)> {
        // TODO: this doesn't need to be calling find_subheap repeatedly
        let layout = Layout::new::<T>();
        let mut latest = self.alloc_raw(layout);
        if latest.is_none() {
            self.heap.gc();
            latest = self.alloc_raw(layout);
            if latest.is_none() {
                // SAFETY: always can deref state
                let subheap = self
                    .state
                    .as_ref()
                    .find_subheap(layout.align_to(8).expect("address arith error?").size())?;
                let newseg = self.heap.new_segment(layout, subheap)?;
                subheap.set_segment::<Hdr>(layout, newseg);
                latest = self.alloc_raw(layout);
                latest?;
            }
        }
        //todo!("insert vtable into segment table if not already present.");
        latest.map(|x| {
            core::ptr::write(x.cast().as_ptr(), val);
            let obj = transmute::<&(dyn crate::Trace + Sync), core::raw::TraitObject>(
                x.cast::<T>().as_ref(),
            );
            let (seg, ix) = self.heap.segment_and_idx(x);
            let hdr = (*seg).header_from_index::<Hdr>(ix);
            // TODO: PERF: scanning the trace tables in alloc really sucks, can we avoid that?
            match (*seg)
                .trace_tables
                .iter()
                .enumerate()
                .find(|(_, &vt)| obj.vtable == vt)
            {
                Some((n, _)) => hdr.as_ref().list_link.set(Packed::from_pointer_and_bits(
                    transmute::<&ObjHdr<Hdr>, &'static ObjHdr<Hdr>>(hdr.as_ref()),
                    n,
                )),
                None => {
                    // not yet present in the trace tables...
                    (*seg).trace_tables[(*seg).trace_count.get() as usize] = obj.vtable;
                    (*seg).trace_count.update(|x| x + 1);
                }
            }
            (x.cast(), NonNull::from(&hdr.as_ref().data))
        })
    }

    /// Mark a pointer as a root. Roots are considered live even if the GC does not
    /// trace any references to it.
    pub fn add_root_mark(&self, _ptr: NonNull<u8>) {
        todo!()
    }

    /// Remove the root mark from a pointer, allowing it to be collected when the
    /// GC determines it is unreachable.
    pub fn remove_root_mark(&self, _ptr: NonNull<u8>) {
        todo!()
    }
}

impl<Hdr: 'static> core::fmt::Debug for HeapRegistration<Hdr> {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.write_str("HeapRegistration")
    }
}

impl<Hdr: 'static> Drop for HeapRegistration<Hdr> {
    fn drop(&mut self) {
        // SAFETY: always safe to access our thread state
        let state = unsafe { self.state.as_ref() };
        state.check_gc();
        if state.viewers.fetch_sub(1, AcqRel) == 0 {
            // TODO: is there anything we even need to do?
        }
    }
}

impl<Hdr: 'static> Heap<Hdr> {
    /// Start using this heap on this thread, pinning the heap until
    /// the final `HeapRegistration` created on this thread is dropped.
    ///
    /// If this thread is already using the GC,
    /// Returns `None` if we are already using this thread. If this is the first
    /// time start is called on this thread, blocks until the garbage collector
    /// stops its current collection and lets us enter the thread list.
    pub fn start(self: Pin<Arc<Heap<Hdr>>>) -> HeapRegistration<Hdr> {
        let not_yet_my_thread = self.cur_thread.read();
        let heap = self.clone();
        let state = not_yet_my_thread.get_or(|| ThreadState {
            state: crate::heap::AtomicState::new(self.initstate.load(Acquire)),
            // SAFETY: the next pointers in the self object headers always point to the correct type
            barrier: ObjList(Some(Packed::from_pointer_and_bits(
                unsafe { &*(&self.barrier as *const _ as *const _) },
                0,
            ))),
            tmproot: UnsafeCell::new(ObjList(Some(Packed::from_pointer_and_bits(
                unsafe { &*(&self.roots as *const _ as *const _) },
                0,
            )))),
            heap: Arc::downgrade(&Pin::into_inner(heap)),
            subheaps: UnsafeCell::new(Default::default()),
            viewers: 0.into(),
            roots: UnsafeCell::new(vec![]),
            _pin: core::marker::PhantomPinned,
        });
        let state = NonNull::from(state);
        drop(not_yet_my_thread);
        HeapRegistration { state, heap: self }
    }

    /// Create a new managed heap sourcing blocks from the system allocator.
    pub fn new() -> Pin<Arc<Heap<Hdr>>> {
        Heap::from_alloc(Box::new(std::alloc::System) as Box<dyn GlobalAlloc + Send>)
    }

    /// Create a garbage collected heap which uses `alloc` as a sub-allocator for
    /// large blocks which the garbage collector then splits and manages. `alloc`
    /// may be called from different threads.
    pub fn from_alloc(alloc: Box<dyn GlobalAlloc + Send>) -> Pin<Arc<Heap<Hdr>>> {
        Pin::new(Arc::new(Heap {
            block_alloc: BlockAlloc(Mutex::new(alloc)),
            segment_mask: (1 << 15) - 1, // 32KiB - 1
            initstate: AtomicState::new(State::Async),
            cur_thread: RwLock::new(CachedThreadLocal::new()),
            roots: ObjectHeader::new(()),
            free: ObjectHeader::new(()),
            barrier: ObjectHeader::new(()),
            subheap_roots: UnsafeCell::new(Default::default()),
            handshake: crate::handshake::Handshake::new(),
            global_trace: [core::ptr::null_mut(); 4],
        }))
    }
}

/// GC metrics.
pub enum MetricEvent {
    TookSegment { free_slots: usize },
    Snapshot { duration: std::time::Duration },
}
