mod sais;

use std::fmt::Debug;
use std::{iter::zip, ops::Deref};

use crate::index::{self, fits, ArrayIndex};
use crate::TextExt;

/// TODO: Invariants:
/// - sa is permutation of (0, sa.len())
#[derive(Debug, Clone)]
pub struct SuffixArray<Idx: ArrayIndex = usize>(Box<[Idx]>);

impl<Idx: ArrayIndex> Deref for SuffixArray<Idx> {
    type Target = [Idx];

    fn deref(&self) -> &Self::Target { &self.0 }
}

impl<Idx: ArrayIndex> SuffixArray<Idx> {
    #[inline(never)]
    pub fn inverse(&self) -> InverseSuffixArray {
        // TODO use MaybeUninit for optimization

        let mut isa = vec![0; self.len()];

        for (i, sa_i) in self.iter().enumerate() {
            // SAFETY: Because a SuffixArray is a permutation of (0, len),
            // sa_i is guaranteed to not be out of bounds for isa
            unsafe { *isa.get_unchecked_mut(sa_i.to_usize()) = i };
        }

        InverseSuffixArray(isa.into_boxed_slice())
    }

    // TODO move to test module
    #[allow(unused)]
    pub fn verify<T: Ord + Debug>(&self, text: &[T]) {
        assert!(zip(self.0.iter(), self.0.iter().skip(1)).all(|(i, j)| {
            text.suffix(i.to_usize()) < text.suffix(j.to_usize())
        }));

        let mut arr = vec![false; text.len()];
        self.0.iter().for_each(|i| arr[i.to_usize()] = true);
        assert_eq!(arr, vec![true; text.len()]);
    }
}

/// TODO: Invariants:
/// - sa is permutation of (0, sa.len())
#[derive(Debug, Clone)]
pub struct InverseSuffixArray<Idx: ArrayIndex = usize>(Box<[Idx]>);

impl<Idx: ArrayIndex> Deref for InverseSuffixArray<Idx> {
    type Target = [Idx];

    fn deref(&self) -> &Self::Target { &self.0 }
}

#[allow(unused)]
pub fn naive<T: Ord + Debug, Idx: ArrayIndex>(text: &[T]) -> SuffixArray<Idx> {
    // TODO This should return a result instead
    assert!(index::fits::<Idx, _>(text));

    let mut sa: Box<_> = (0..text.len()).map(Idx::from_usize).collect();
    sa.sort_by_key(|i| text.suffix(i.to_usize()));

    SuffixArray(sa)
}

pub fn sais(text: &[u8]) -> SuffixArray {
    let sa = sais::sais(text);
    sa.verify(text);
    sa
}
