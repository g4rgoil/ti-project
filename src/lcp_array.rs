use std::iter::zip;
use std::ops::Deref;

use crate::suffix_array::InverseSuffixArray;
use crate::suffix_array::SuffixArray;
use crate::TextExt;

#[derive(Debug, Clone)]
pub struct LCPArray(Box<[usize]>);

impl Deref for LCPArray {
    type Target = [usize];

    fn deref(&self) -> &Self::Target { &self.0 }
}

pub fn naive<T: Ord>(text: &[T], sa: &SuffixArray) -> LCPArray {
    assert_eq!(text.len(), sa.len());

    // TODO don't use extend

    let mut lcp = Vec::with_capacity(text.len());
    lcp.extend(text.first().map(|_| 0));


    // TODO lcp.extend(zip(sa.iter(), sa.iter().skip(1)).map(|(i, j)| {
    lcp.extend(sa.array_windows::<2>().map(|[i, j]| {
        let suffix_i = text.suffix(*i);
        let suffix_j = text.suffix(*j);
        common_prefix(suffix_i, suffix_j)
    }));

    LCPArray(lcp.into_boxed_slice())
}

pub fn kasai<T: Ord>(
    text: &[T],
    sa: &SuffixArray,
    isa: &InverseSuffixArray,
) -> LCPArray {
    assert_eq!(text.len(), sa.len());

    let mut lcp = vec![0; text.len()];

    let mut l = 0;
    for (i, &isa_i) in isa.iter().enumerate() {
        if isa_i != 0 {
            let j = sa[isa_i - 1];
            let suffix_i_l = text.suffix(i + l);
            let suffix_j_l = text.suffix(j + l);
            l += common_prefix(suffix_i_l, suffix_j_l);

            lcp[isa_i] = l;
            l = l.saturating_sub(1);
        }
    }

    LCPArray(lcp.into_boxed_slice())
}

pub fn phi<T: Ord>(text: &[T], sa: &SuffixArray) -> LCPArray {
    // TODO use MaybeUninit for optimization

    let mut phi = vec![0; sa.len()];
    for (i, &sa_i) in sa.iter().enumerate().skip(1) {
        phi[sa_i] = sa[i - 1];
    }

    let mut l = 0;
    for (i, j) in phi.iter_mut().enumerate() {
        let suffix_i_l = text.suffix(i + l);
        let suffix_j_l = text.suffix(*j + l);

        *j = l + common_prefix(suffix_i_l, suffix_j_l);
        l = j.saturating_sub(1);
    }

    LCPArray(sa.iter().map(|&sa_i| phi[sa_i]).collect())
}

fn common_prefix<T: Ord>(lhs: &[T], rhs: &[T]) -> usize {
    zip(lhs, rhs).take_while(|(l, r)| l == r).count()
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::suffix_array as sa;

    #[test]
    fn test_empty_text() {
        let text = b"";
        let sa = &sa::naive(text);
        let isa = &sa.inverse();

        assert_eq!(*naive(text, sa), []);
        assert_eq!(*kasai(text, sa, isa), []);
        assert_eq!(*phi(text, sa), []);
    }

    #[test]
    fn test_simple_text() {
        let text = b"banana";
        let sa = &sa::naive(text);
        let isa = &sa.inverse();
        let lcp = [0, 1, 3, 0, 0, 2];

        assert_eq!(*naive(text, &sa), lcp);
        assert_eq!(*kasai(text, &sa, &isa), lcp);
        assert_eq!(*phi(text, &sa), lcp);
    }

    #[test]
    #[ignore = "need to fix handling of first char"]
    fn test_lcp_slides() {
        let text = b"ababcabcabba";
        let sa = &sa::naive(text);
        let isa = &sa.inverse();
        let naive_lcp = naive(text, &sa);

        assert_eq!(*kasai(text, &sa, &isa), *naive_lcp);
        assert_eq!(*phi(text, &sa), *naive_lcp);
    }

    #[test]
    #[ignore = "need to fix handling of first char"]
    fn test_lcp_wikipedia() {
        let text = b"immissiissippi";
        let sa = &sa::naive(text);
        let isa = &sa.inverse();
        let naive_lcp = naive(text, &sa);

        assert_eq!(*kasai(text, &sa, &isa), *naive_lcp);
        assert_eq!(*phi(text, &sa), *naive_lcp);
    }
}
