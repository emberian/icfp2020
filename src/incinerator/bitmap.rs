use core::cell::Cell;

/// A "tree-structured bitmap". Honestly just see the paper for details, it has
/// diagrams and such that make it all much easier to understand.
///
/// Contracts are pseudo-Hoare notation. `{pre} stmt {post}` means that if
/// `{pre}` holds prior to the stmt executing, `post` holds afterwards.
#[derive(PartialEq, Debug, Clone, Eq, Default)]
pub struct Bitmap {
    // TODO: uhhh store this inline in the segment?
    // TODO: FIXME: uhhhhhhh stop vec vec
    pub(crate) arrays: Vec<Vec<Cell<u32>>>,
}

// TODO: benchmark and see if u32 wins over u64 here
// paper uses u32, so *shrug*. i suspect u64 mask will win
// as it will need to dispatch half as many next_mask ops?
#[derive(Copy, Clone, Debug, Default)]
pub struct Bitptr {
    index: u32,
    mask: u32,
}

#[derive(Copy, Clone, Debug)]
pub enum Result {
    Failure,
    Success,
}
use self::Result::*;

impl Bitptr {
    pub fn from_index(index: u32) -> Bitptr {
        // 2^5 (32) bits per u32...
        let (ix, bitidx) = ((index & !31) >> 5, index & 31);
        Bitptr {
            index: ix as u32,
            mask: 1 << bitidx,
        }
    }

    // HOTPATH
    #[inline]
    pub fn to_index(&self) -> u32 {
        (self.index << 5) | (self.mask - 1)
    }
}

impl Bitmap {
    // TODO: less copypasta?
    pub fn new(total_count: usize) -> Bitmap {
        use crate::segment::{log2, roundup};
        let mut div = 1;
        Bitmap {
            arrays: (0usize..=log2((total_count + 31) / 32))
                .map(|_| {
                    let elems_this_level = roundup(total_count / 32) / div;
                    div *= 32;
                    vec![Cell::new(0u32); elems_this_level]
                })
                .collect(),
        }
    }
    #[cfg(test)]
    pub fn unset(&mut self, cursor: &mut [Bitptr], level: usize) {
        for level in level..self.arrays.len() {
            if let Some(Bitptr { index, mask }) = cursor.get(level) {
                if let Some(c) = self.arrays.get(level).and_then(|v| v.get(*index as usize)) {
                    c.update(|v| v & !mask);
                    if level + 1 < self.arrays.len() && c.get() == u32::MAX {
                        cursor[level + 1] = Bitptr::from_index(*index);
                    }
                }
            }
            unreachable!("sadness! we didn't preallocate thoroughly enough");
        }
    }

    pub fn set(&mut self, cursor: &mut [Bitptr], level: usize) {
        assert_eq!(cursor.len(), self.arrays.len());
        for level in level..self.arrays.len() {
            if let Some(Bitptr { index, mask }) = cursor.get(level) {
                if let Some(c) = self.arrays.get(level).and_then(|v| v.get(*index as usize)) {
                    c.update(|v| v | mask);
                    if level + 1 < self.arrays.len() && c.get() == u32::MAX {
                        cursor[level + 1] = Bitptr::from_index(*index);
                        continue;
                    }
                    return;
                }
            }
            unreachable!("sadness! we didn't preallocate thoroughly enough");
        }
    }

    /// Start containing `val`.
    ///
    /// Contract:
    ///
    /// ```txt
    /// {oldbm = bm.clone()}
    /// bm.add(v);
    /// {forall x. if x == v then bm.contains(v) == true else bm.contains(v) == oldbm.contains(v)}
    /// ```
    #[cfg(test)]
    pub fn add(&mut self, val: u32) {
        self.set(&mut vec![Bitptr::from_index(val); self.arrays.len()], 0);
        println!("{:?}", self);
        #[cfg(test)]
        assert!(self.contains(val));
    }

    /// Stop containing `val`.
    ///
    /// Contract:
    ///
    /// ```txt
    /// {oldbm = bm.clone()}
    /// bm.remove(v);
    /// {forall x. if x == v then bm.contains(v) == false else bm.contains(v) == oldbm.contains(v)}
    /// ```
    #[cfg(test)]
    pub fn remove(&mut self, val: u32) {
        #[cfg(test)]
        let c = self.contains(val);
        self.unset(&mut vec![Bitptr::from_index(val); self.arrays.len()], 0);
        #[cfg(test)]
        assert!(c, !self.contains(val));
    }

    /// Do we currently contain `val`?
    ///
    /// Contract: `{} bm.contains(v) {}`
    pub fn contains(&self, val: u32) -> bool {
        let Bitptr { index, mask } = Bitptr::from_index(val);
        if let Some(v) = self.arrays.get(0).and_then(|a| a.get(index as usize)) {
            v.get() & mask != 0
        } else {
            false
        }
    }

    /// Cause the map to contain nothing.
    ///
    /// Contract: `{} bm.clear() {forall x. !bm.contains(x)}`
    pub fn clear(&mut self) {
        for arr in self.arrays.iter() {
            // TODO: memset?
            for val in arr.iter() {
                val.set(0);
            }
        }
    }

    /// Cause the map to contain nothing.
    ///
    /// Contract: `{oldi = i.clone()} bm.from_iter(i) {forall x. bm.contains(x) == oldi.contains(x)}`
    #[cfg(test)]
    pub fn from_iter<I: core::iter::ExactSizeIterator + IntoIterator<Item = u32>>(i: I) -> Bitmap {
        println!("{}", i.len());
        let mut this = Bitmap::new(i.len());
        for v in i.into_iter() {
            this.add(v);
        }
        this
    }

    /// Advanced the mask in the bitptr for level, causing it to select the next
    /// free slot.
    fn next_mask(&self, cursor: &mut [Bitptr], level: usize) -> Option<()> {
        // FIXME: actually think about this bit math. is there anything useful here?
        let val = self
            .arrays
            .get(level)?
            .get(cursor.get(level)?.index as usize)?
            .get();
        // mask= 000000000000000001000000000000
        //   -1= 000000000000000000111111111111
        // val = 00000.......010111011010101110
        // |     ^                ^           ^
        // |     31             bitidx        0
        let val = val | (cursor.get(level)?.mask - 1);
        //          new_bitidx--v
        // val = 00000.......010111111111111111
        // |     ^                ^           ^
        // |     31             bitidx        0
        let new_bitidx = val.trailing_ones() as u64 - 1;
        if new_bitidx <= 31 {
            cursor.get_mut(level)?.mask = 1 << new_bitidx;
            Some(())
        } else {
            None
        }
    }

    // TODO: benchmark w and w/out boundschecks
    fn advance(&self, cursor: &mut [Bitptr], level: usize) -> Option<()> {
        // forwardBitPtr(P_i, j)
        if level + 1 >= self.arrays.len() {
            return None;
        }
        let bitptr = Bitptr::from_index(cursor.get(level)?.index);
        *cursor.get_mut(level + 1)? = bitptr;
        if self.next_mask(cursor, level).is_none() {
            self.advance(cursor, level + 1)?;
        }
        *cursor.get_mut(level)? = Bitptr {
            index: cursor.get(level + 1)?.to_index(),
            mask: 1,
        };
        assert!(self.next_mask(cursor, level).is_some());
        Some(())
    }

    /// Return the first value after `cursor` that is not present in the map.
    ///
    /// Contract:
    ///
    /// ```txt
    /// {after != u64::MAX}
    /// res = bm.next_not_contained(after)
    /// {res = Some(res) ==> !bm.contains(res) && forall x. x > after && x < res ==> bm.contains(x)}
    /// {res = None ==> forall x. x > after ==> bm.contains(x)}
    /// ```
    // HOTPATH
    #[inline]
    pub fn next_not_contained(&self, cursor: &mut [Bitptr]) -> Result {
        if self.next_mask(cursor, 0).is_none() {
            if self.advance(cursor, 0).is_none() {
                return Failure;
            }
        }
        Success
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[quickcheck_macros::quickcheck]
    fn equiv_with_vec(data: Vec<u16>) -> bool {
        let bm = Bitmap::from_iter(data.iter().map(|&x| x as u32));
        // check the forall manually
        for v in 0..u16::MAX {
            if data.contains(&v) != bm.contains(v as u32) {
                return false;
            }
        }
        true
    }

    fn next_not_contained_prop(data: &[u16]) -> bool {
        std::panic::catch_unwind(|| {
            let bm = Bitmap::from_iter(data.iter().map(|&x| x as u32));
            let mut cursor = vec![Bitptr::from_index(0); bm.arrays.len()];
            for v in 0..u16::MAX - 1 {
                cursor[0] = Bitptr::from_index(v as u32);
                match bm.next_not_contained(&mut cursor) {
                    Success => assert!(!data.contains(&(cursor[0].to_index() as u16))),
                    Failure => {
                        // check the forall manually
                        for iv in v + 1.. {
                            if !data.contains(&iv) {
                                println!("{:?}\n{:?}\n{:?}\n{:?}", data, v, iv, bm);
                            }
                            assert!(data.contains(&v));
                        }
                    }
                }
            }
        })
        .is_ok()
    }

    #[quickcheck_macros::quickcheck]
    fn next_not_contained(data: Vec<u16>) -> bool {
        next_not_contained_prop(&*data)
    }

    #[test]
    fn old_next_bugs() {
        assert!(next_not_contained_prop(&[0]));
        assert!(next_not_contained_prop(&[64]));
    }

    #[test]
    fn next_contained_limits() {
        let bm = Bitmap::new(1 << 14);
        assert!(matches!(
            bm.next_not_contained(&mut vec![Bitptr::from_index(1 << 14); 12]),
            Failure
        ));
        assert!(matches!(
            bm.next_not_contained(&mut vec![Bitptr::from_index((1 << 14) - 2); 12]),
            Success
        ));
    }

    #[quickcheck_macros::quickcheck]
    fn remove(mut data: Vec<u16>) -> bool {
        data.sort();
        data.dedup();
        let mut bm = Bitmap::from_iter(data.iter().map(|&x| x as u32));
        while let Some(d) = data.pop() {
            // FIXME: test more removal patterns?
            bm.remove(d as u32);
            for &v in &data {
                assert!(bm.contains(v as u32));
            }
        }
        true
    }
}
