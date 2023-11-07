use parking_lot::{Condvar, Mutex};
use std::sync::atomic::{
    AtomicUsize,
    Ordering::{AcqRel, Acquire, Release},
};

/// The handshake acts like a `std::sync::Barrier`, but only the collector
/// actually blocks on it. It is used to ensure that all threads have
/// acknowledged a global state transition before the collector continues.
#[derive(Debug)]
pub struct Handshake {
    count: AtomicUsize,
    expected: AtomicUsize,
    lock: Mutex<()>,
    condvar: Condvar,
}

impl Handshake {
    pub fn new() -> Handshake {
        Handshake {
            count: 0.into(),
            expected: 0.into(),
            lock: Mutex::new(()),
            condvar: Condvar::new(),
        }
    }

    /// Signal that the current thread is ready.
    pub fn increment(&self) {
        if self.count.fetch_add(1, AcqRel) == self.expected.load(Acquire) - 1 {
            self.condvar.notify_all();
        }
    }

    /// Wait until the expected number of threads have called increment.
    pub fn wait(&self) {
        // CORRECTNESS:
        if self.count.load(Acquire) != self.expected.load(Acquire) {
            let mut condlock = self.lock.lock();
            self.condvar.wait(&mut condlock);
            self.count.store(0, Release);
        }
    }

    /// Expect `count` threads next time we call `wait`.
    ///
    /// ## Concurrency correctness
    ///
    /// There should be no concurrenct calls to `increment` between a return from
    /// `wait` and a call to `set_expected_count`. Otherwise, the waiter will
    /// be woken either prematurely or never.
    pub fn set_expected_count(&self, count: usize) {
        self.expected.store(count, Release);
    }
}

// TODO: how to thoroughly test such a thing?

#[test]
fn smoke() {
    let hs = std::sync::Arc::new(Handshake::new());

    // first, test that we can spawn 8 threads incrementing it..

    hs.set_expected_count(8);
    for _ in 0..8 {
        let ours = hs.clone();
        core::mem::forget(std::thread::spawn(move || ours.increment()));
    }
    hs.wait(); // the test "passes" if this doesn't hang.

    // and continue to spawn a thread that will eventually increment with eight
    // threads, and we will hope to be blocked on our wait before those go.
    let threadhs = hs.clone();
    core::mem::forget(std::thread::spawn(move || {
        // just enough to hit the wait below..
        std::thread::sleep(std::time::Duration::from_millis(50));
        for _ in 0..8 {
            let ours = threadhs.clone();
            core::mem::forget(std::thread::spawn(move || ours.increment()));
        }
    }));

    hs.wait();
}
