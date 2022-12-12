mod sais;

use std::fmt::Debug;
use std::{iter::zip, ops::Deref};

use crate::TextExt;

/// TODO: Invariants:
/// - sa is permutation of (0, sa.len())
#[derive(Debug, Clone)]
pub struct SuffixArray(Box<[usize]>);

impl Deref for SuffixArray {
    type Target = [usize];

    fn deref(&self) -> &Self::Target { &self.0 }
}

impl SuffixArray {
    #[inline(never)]
    pub fn inverse(&self) -> InverseSuffixArray {
        // TODO use MaybeUninit for optimization

        let mut isa = vec![0; self.len()];

        for (i, sa_i) in self.iter().enumerate() {
            // SAFETY: Because a SuffixArray is a permutation of (0, len),
            // sa_i is guaranteed to not be out of bounds for isa
            unsafe { *isa.get_unchecked_mut(*sa_i) = i };
        }

        InverseSuffixArray(isa.into_boxed_slice())
    }

    // TODO move to test module
    #[allow(unused)]
    pub fn verify<T: Ord + Debug>(&self, text: &[T]) {
        assert!(zip(self.0.iter(), self.0.iter().skip(1))
            .all(|(i, j)| text.suffix(*i) < text.suffix(*j)));

        let mut arr = vec![false; text.len()];
        self.0.iter().for_each(|i| arr[*i] = true);
        assert!(arr.into_iter().all(|b| b));
    }
}

/// TODO: Invariants:
/// - sa is permutation of (0, sa.len())
#[derive(Debug, Clone)]
pub struct InverseSuffixArray(Box<[usize]>);

impl Deref for InverseSuffixArray {
    type Target = [usize];

    fn deref(&self) -> &Self::Target { &self.0 }
}

#[allow(unused)]
pub fn naive<T: Ord + Debug>(text: &[T]) -> SuffixArray {
    let mut sa: Box<_> = (0..text.len()).collect();
    sa.sort_by_key(|i| text.suffix(*i));

    // TODO remove
    let sa = SuffixArray(sa);
    sa.verify(text);
    sa
}

pub fn sais(text: &[u8]) -> SuffixArray {
    let sa = sais::sais(text);
    sa.verify(text);
    sa
}
