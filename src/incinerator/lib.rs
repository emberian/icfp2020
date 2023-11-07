#![feature(
    alloc_layout_extra,
    cell_update,
    raw,
    maybe_uninit_ref,
    maybe_uninit_extra
)]

//! An exact, tracing, non-moving, unobtrusive concurrent garbage collector.
//!
//! This library is an implementation of the Ueno-Ohori concurrent garbage
//! collector, as described in the [ICFP'16 paper by
//! aforementioned](https://www.pllab.riec.tohoku.ac.jp/papers/icfp2016UenoOhori-preprint.pdf).
//!
//! It itself is an adaptation of a [previous non-copying garbage
//! collector](https://www.pllab.riec.tohoku.ac.jp/papers/icfp2011UenoOhoriOtomoAuthorVersion.pdf)
//! of theirs to a concurrent setting.
//!
//! ## Using
//!
//! TODO: how to allocate + use objects.
//! TODO: details of how to become traced.
//! TODO: details on how to enter/exit GC contexts in each thread.
//!
//! ## Internals and overhead
//!
//! TODO: describe the internal data structures
//! TODO: heap overhead, asymptotically and in practice.

extern crate alloc;

mod api;
mod bitmap;
mod handshake;
mod heap;
mod segment;
mod trace;

pub use api::*;
pub use heap::Heap;
pub use trace::*;

fn instrument<T>(_label: &'static str, f: impl FnOnce() -> T) -> T {
    // TODO: actually measure and record how long this took
    f()
}

#[cfg(test)]
mod tests {
    #[test]
    fn smoke() {
        let h = crate::Heap::<()>::new();
        let our_reg = h.start(); //.expect("this thread already using this heap? how?");
        let u64_obj = unsafe { our_reg.alloc(8u64) };
        u64_obj.expect("alloc failed? :(");
        our_reg.gc();
    }
}
