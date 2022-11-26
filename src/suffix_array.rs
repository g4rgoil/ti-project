mod sais;

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

    #[allow(unused)]
    pub fn is_correct<T: Ord>(&self, text: &[T]) -> bool {
        assert!(zip(self.0.iter(), self.0.iter().skip(1))
            .all(|(i, j)| text.suffix(*i) < text.suffix(*j)));

        let mut arr = vec![false; text.len()];
        self.0.iter().for_each(|i| arr[*i] = true);
        assert!(arr.into_iter().all(|b| b));
        true
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
pub fn naive<T: Ord>(text: &[T]) -> SuffixArray {
    let mut sa: Box<_> = (0..text.len()).collect();
    sa.sort_by_key(|i| text.suffix(*i));

    // TODO remove
    let sa = SuffixArray(sa);
    assert!(sa.is_correct(text));
    sa
}

pub fn sais(text: &[u8]) -> SuffixArray {
    let sa = sais::construct(text);
    assert!(sa.is_correct(text));
    sa
}


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_empty_text() {
        assert_eq!(*naive(b""), []);
    }

    #[test]
    fn test_simple_text() {
        let text = b"banana";
        let sa = [5, 3, 1, 0, 4, 2];

        assert_eq!(*naive(text), sa);
        assert_eq!(*sais(text), sa);
    }

    #[test]
    fn test_isa_empty() {
        let sa = SuffixArray(Box::new([]));

        assert_eq!(*sa.inverse(), []);
    }
}
