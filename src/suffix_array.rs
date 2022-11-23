use std::ops::Deref;

use crate::TextExt;

/// TODO: Invariants:
/// - sa is permutation of (0, sa.len())
#[derive(Debug, Clone)]
pub struct SuffixArray(Box<[usize]>);

impl Deref for SuffixArray {
    type Target = [usize];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl SuffixArray {
    pub fn inverse(&self) -> InverseSuffixArray {
        // TODO use MaybeUninit for optimization

        let mut isa = vec![0; self.len()];
        for (i, sa_i) in self.iter().enumerate() {
            // TODO elide bound checks
            isa[*sa_i] = i;
        }

        InverseSuffixArray(isa.into_boxed_slice())
    }
}

/// TODO: Invariants:
/// - sa is permutation of (0, sa.len())
#[derive(Debug, Clone)]
pub struct InverseSuffixArray(Box<[usize]>);

impl Deref for InverseSuffixArray {
    type Target = [usize];

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub fn naive<T: Ord>(text: &[T]) -> SuffixArray {
    let mut sa: Box<_> = (0..text.len()).collect();
    sa.sort_by(|l, r| text.suffix(*l).cmp(text.suffix(*r)));
    SuffixArray(sa)
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
    }

    #[test]
    fn test_isa_empty() {
        let sa = SuffixArray(Box::new([]));

        assert_eq!(*sa.inverse(), []);
    }
}
