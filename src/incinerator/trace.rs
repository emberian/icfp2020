// tweaked from https://github.com/Manishearth/rust-gc/blob/563f685972d98d3608b52a82bbfef811d89abc54/gc/src/trace.rs

// all i did was add the callback

use alloc::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};
use alloc::rc::Rc;
use core::hash::{BuildHasher, Hash};
use core::num::{
    NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroIsize, NonZeroU128,
    NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize,
};
use core::sync::atomic::{
    AtomicBool, AtomicI16, AtomicI32, AtomicI64, AtomicI8, AtomicIsize, AtomicU16, AtomicU32,
    AtomicU64, AtomicU8, AtomicUsize,
};
use std::{
    collections::{HashMap, HashSet},
    path::{Path, PathBuf},
};

/// The Finalize trait. Can be specialized for a specific type to define
/// finalization logic for that type.
pub trait Finalize {
    fn finalize(&self) {}
}

//impl<T: ?Sized> Finalize for T {
//    // Should this function somehow tell its caller (which is presumably
//    // the GC runtime) that it did nothing?
//    #[inline]
//    default fn finalize(&self) {}
//}

/// The Trace trait, which needs to be implemented on garbage-collected objects.
pub unsafe trait Trace: Finalize {
    /// Visit each contained gc'd pointer (by reference).
    ///
    /// # Safety
    ///
    /// If you store a gc pointer, and do not list it when visited, it may be
    /// deallocated and thus a memory unsafety sadness will be had. So please
    /// be careful :)
    unsafe fn visit(&self, _heap: &crate::Heap<()>, cb: &dyn Fn(&usize));

    /// Runs Finalize::finalize() on this object and all
    /// contained subobjects
    fn finalize_glue(&self);
}

/// This rule implements the trace methods with empty implementations.
///
/// Use this for marking types as not containing any `Trace` types.
#[macro_export]
macro_rules! unsafe_empty_trace {
    () => {
        #[inline]
        #[allow(unused_variables)]
        unsafe fn visit(&self, _heap: &$crate::Heap<()>, cb: &dyn Fn(&usize)) {}
        #[inline]
        fn finalize_glue(&self) {
            $crate::Finalize::finalize(self)
        }
    };
}

/// This rule implements the trace method.
///
/// You define a `this` parameter name and pass in a body, which should call `mark!(x)` on every
/// traceable element inside the body. The mark implementation will automatically delegate to the
/// correct method on the argument.
#[macro_export]
macro_rules! custom_trace {
    ($this:ident, $heap:ident, $cb:ident, $body:expr) => {
        #[inline]
        unsafe fn visit(&self, $heap: &$crate::Heap<()>, $cb: &dyn Fn(&usize)) {
            macro_rules! mark {
                ($thing:expr) => {
                    $crate::Trace::visit($thing, $heap, $cb);
                };
            }
            let $this = self;
            $body
        }
        #[inline]
        fn finalize_glue(&self) {
            $crate::Finalize::finalize(self);
            #[inline]
            fn mark<T: $crate::Trace + ?Sized>(it: &T) {
                $crate::Trace::finalize_glue(it);
            }
            macro_rules! mark {
                ($thing:expr) => {
                    mark($thing);
                };
            }
            let $this = self;
            $body
        }
    };
    ($this:ident, $body:expr) => {
        $crate::custom_trace!($this, _heap, _cb, $body);
    };
}

impl<T: ?Sized> Finalize for &'static T {}
unsafe impl<T: ?Sized> Trace for &'static T {
    unsafe_empty_trace!();
}

macro_rules! simple_empty_finalize_trace {
    ($($T:ty),*) => {
        $(
            impl Finalize for $T {}
            unsafe impl Trace for $T { unsafe_empty_trace!(); }
        )*
    }
}

simple_empty_finalize_trace![
    (),
    bool,
    isize,
    usize,
    i8,
    u8,
    i16,
    u16,
    i32,
    u32,
    i64,
    u64,
    i128,
    u128,
    f32,
    f64,
    char,
    String,
    Box<str>,
    Rc<str>,
    Path,
    PathBuf,
    NonZeroIsize,
    NonZeroUsize,
    NonZeroI8,
    NonZeroU8,
    NonZeroI16,
    NonZeroU16,
    NonZeroI32,
    NonZeroU32,
    NonZeroI64,
    NonZeroU64,
    NonZeroI128,
    NonZeroU128,
    AtomicBool,
    AtomicIsize,
    AtomicUsize,
    AtomicI8,
    AtomicU8,
    AtomicI16,
    AtomicU16,
    AtomicI32,
    AtomicU32,
    AtomicI64,
    AtomicU64
];

macro_rules! array_finalize_trace {
    ($n:expr) => {
        impl<T: Trace> Finalize for [T; $n] {}
        unsafe impl<T: Trace> Trace for [T; $n] {
            custom_trace!(this, {
                for v in this {
                    mark!(v);
                }
            });
        }
    };
}

macro_rules! fn_finalize_trace_one {
    ($ty:ty $(,$args:ident)*) => {
        impl<Ret $(,$args)*> Finalize for $ty {}
        unsafe impl<Ret $(,$args)*> Trace for $ty { unsafe_empty_trace!(); }
    }
}
macro_rules! fn_finalize_trace_group {
    () => {
        fn_finalize_trace_one!(extern "Rust" fn () -> Ret);
        fn_finalize_trace_one!(extern "C" fn () -> Ret);
        fn_finalize_trace_one!(unsafe extern "Rust" fn () -> Ret);
        fn_finalize_trace_one!(unsafe extern "C" fn () -> Ret);
    };
    ($($args:ident),*) => {
        fn_finalize_trace_one!(extern "Rust" fn ($($args),*) -> Ret, $($args),*);
        fn_finalize_trace_one!(extern "C" fn ($($args),*) -> Ret, $($args),*);
        fn_finalize_trace_one!(extern "C" fn ($($args),*, ...) -> Ret, $($args),*);
        fn_finalize_trace_one!(unsafe extern "Rust" fn ($($args),*) -> Ret, $($args),*);
        fn_finalize_trace_one!(unsafe extern "C" fn ($($args),*) -> Ret, $($args),*);
        fn_finalize_trace_one!(unsafe extern "C" fn ($($args),*, ...) -> Ret, $($args),*);
    }
}

macro_rules! tuple_finalize_trace {
    () => {}; // This case is handled above, by simple_finalize_empty_trace!().
    ($($args:ident),*) => {
        impl<$($args),*> Finalize for ($($args,)*) {}
        #[allow(non_snake_case, unused_unsafe)]
        unsafe impl<$($args: $crate::Trace),*> Trace for ($($args,)*) {
            custom_trace!(this, {
                let ($(ref $args,)*) = this;
                unsafe { $(mark!($args);)* }
            });
        }
    }
}

macro_rules! array_finalize_trace_impls {
    ($($n:expr),*) => {
        $(
            array_finalize_trace!($n);
        )*
    }
}
macro_rules! type_arg_tuple_based_finalized_trace_impls {
    ($(($($args:ident),*);)*) => {
        $(
            fn_finalize_trace_group!($($args),*);
            tuple_finalize_trace!($($args),*);
        )*
    }
}

array_finalize_trace_impls![
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31
];
type_arg_tuple_based_finalized_trace_impls![
    ();
    (A);
    (A, B);
    (A, B, C);
    (A, B, C, D);
    (A, B, C, D, E);
    (A, B, C, D, E, F);
    (A, B, C, D, E, F, G);
    (A, B, C, D, E, F, G, H);
    (A, B, C, D, E, F, G, H, I);
    (A, B, C, D, E, F, G, H, I, J);
    (A, B, C, D, E, F, G, H, I, J, K);
    (A, B, C, D, E, F, G, H, I, J, K, L);
];

impl<T: Trace + ?Sized> Finalize for Rc<T> {}
unsafe impl<T: Trace + ?Sized> Trace for Rc<T> {
    custom_trace!(this, {
        mark!(&**this);
    });
}

impl<T: Trace + ?Sized> Finalize for Box<T> {}
unsafe impl<T: Trace + ?Sized> Trace for Box<T> {
    custom_trace!(this, {
        mark!(&**this);
    });
}

impl<T: Trace> Finalize for Vec<T> {}
unsafe impl<T: Trace> Trace for Vec<T> {
    custom_trace!(this, {
        for e in this {
            mark!(e);
        }
    });
}

impl<T: Trace> Finalize for [T] {}
unsafe impl<T: Trace> Trace for [T] {
    custom_trace!(this, {
        for e in this {
            mark!(e);
        }
    });
}

impl<T: Trace> Finalize for Option<T> {}
unsafe impl<T: Trace> Trace for Option<T> {
    custom_trace!(this, {
        if let Some(ref v) = *this {
            mark!(v);
        }
    });
}

impl<T: Trace, E: Trace> Finalize for Result<T, E> {}
unsafe impl<T: Trace, E: Trace> Trace for Result<T, E> {
    custom_trace!(this, {
        match *this {
            Ok(ref v) => mark!(v),
            Err(ref v) => mark!(v),
        }
    });
}

impl<T: Ord + Trace> Finalize for BinaryHeap<T> {}
unsafe impl<T: Ord + Trace> Trace for BinaryHeap<T> {
    custom_trace!(this, {
        for v in this.iter() {
            mark!(v);
        }
    });
}

impl<K: Trace, V: Trace> Finalize for BTreeMap<K, V> {}
unsafe impl<K: Trace, V: Trace> Trace for BTreeMap<K, V> {
    custom_trace!(this, {
        for (k, v) in this {
            mark!(k);
            mark!(v);
        }
    });
}

impl<T: Trace> Finalize for BTreeSet<T> {}
unsafe impl<T: Trace> Trace for BTreeSet<T> {
    custom_trace!(this, {
        for v in this {
            mark!(v);
        }
    });
}

impl<K: Eq + Hash + Trace, V: Trace, S: BuildHasher> Finalize for HashMap<K, V, S> {}
unsafe impl<K: Eq + Hash + Trace, V: Trace, S: BuildHasher> Trace for HashMap<K, V, S> {
    custom_trace!(this, {
        for (k, v) in this.iter() {
            mark!(k);
            mark!(v);
        }
    });
}

impl<T: Eq + Hash + Trace, S: BuildHasher> Finalize for HashSet<T, S> {}
unsafe impl<T: Eq + Hash + Trace, S: BuildHasher> Trace for HashSet<T, S> {
    custom_trace!(this, {
        for v in this.iter() {
            mark!(v);
        }
    });
}

impl<T: Eq + Hash + Trace> Finalize for LinkedList<T> {}
unsafe impl<T: Eq + Hash + Trace> Trace for LinkedList<T> {
    custom_trace!(this, {
        for v in this.iter() {
            mark!(v);
        }
    });
}

impl<T: Trace> Finalize for VecDeque<T> {}
unsafe impl<T: Trace> Trace for VecDeque<T> {
    custom_trace!(this, {
        for v in this.iter() {
            mark!(v);
        }
    });
}
