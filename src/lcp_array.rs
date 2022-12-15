use std::ops::Deref;

use crate::index::{ArrayIndex, ToIndex};
use crate::suffix_array::{InverseSuffixArray, SuffixArray};
use crate::text::Text;

#[derive(Debug, Clone)]
pub struct LCPArray<Idx: ArrayIndex = usize>(Box<[Idx]>);

impl<Idx: ArrayIndex> Deref for LCPArray<Idx> {
    type Target = [Idx];

    fn deref(&self) -> &Self::Target { &self.0 }
}

pub fn naive<T: Ord, Idx: ArrayIndex>(
    text: &Text<T>,
    sa: &SuffixArray<Idx>,
) -> LCPArray<Idx> {
    assert_eq!(text.len(), sa.len());

    // TODO don't use extend

    let mut lcp = Vec::<Idx>::with_capacity(text.len());
    lcp.extend(text.0.first().map(|_| Idx::from_usize(0)));

    let mut iter = sa.iter().peekable();
    while let (Some(&i), Some(&&j)) = (iter.next(), iter.peek()) {
        // TODO maybe push isn't the best thing here
        lcp.push(Text::common_prefix(&text[i..], &text[j..]).to_index());
    }

    LCPArray(lcp.into_boxed_slice())
}

pub fn kasai<T: Ord, Idx: ArrayIndex>(
    text: &Text<T>,
    sa: &SuffixArray<Idx>,
    isa: &InverseSuffixArray<Idx>,
) -> LCPArray<Idx> {
    assert_eq!(text.len(), sa.len());

    let mut lcp = vec![Idx::ZERO; text.len()];

    let mut l = 0;
    for (i, &isa_i) in isa.iter().enumerate() {
        if isa_i != Idx::ZERO {
            let j = sa[isa_i.as_() - 1];
            let suffix_i_l = &text[i + l..];
            let suffix_j_l = &text[j.as_() + l..];
            l += suffix_i_l.common_prefix(suffix_j_l);

            lcp[isa_i.as_()] = l.to_index();
            l = l.saturating_sub(1);
        }
    }

    LCPArray(lcp.into_boxed_slice())
}

pub fn phi<T: Ord, Idx: ArrayIndex>(
    text: &Text<T>,
    sa: &SuffixArray<Idx>,
) -> LCPArray<Idx> {
    // TODO use MaybeUninit for optimization

    let mut phi = vec![Idx::ZERO; sa.len()];
    for (i, &sa_i) in sa.iter().enumerate().skip(1) {
        phi[sa_i.as_()] = sa[i - 1];
    }

    let mut l = 0;
    for (i, j) in phi.iter_mut().enumerate() {
        let suffix_i_l = &text[i + l..];
        let suffix_j_l = &text[j.as_() + l..];

        *j = (l + suffix_i_l.common_prefix(suffix_j_l)).to_index();
        l = j.as_().saturating_sub(1);
    }

    LCPArray(sa.iter().map(|&sa_i| phi[sa_i.as_()]).collect())
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::suffix_array as sa;

    // TODO I need more tests here
    // TODO need verify() like for SA

    #[test]
    fn test_empty_text() {
        let text = b"".into();
        let sa = &sa::naive::<_, usize>(text);
        let isa = &sa.inverse();

        assert_eq!(*naive(text, sa), []);
        assert_eq!(*kasai(text, sa, isa), []);
        assert_eq!(*phi(text, sa), []);
    }

    #[test]
    fn test_simple_text() {
        let text = b"banana".into();
        let sa = &sa::naive::<_, usize>(text);
        let isa = &sa.inverse();
        let lcp = [0, 1, 3, 0, 0, 2];

        assert_eq!(*naive(text, &sa), lcp);
        assert_eq!(*kasai(text, &sa, &isa), lcp);
        assert_eq!(*phi(text, &sa), lcp);
    }

    #[test]
    #[ignore = "need to fix handling of first char"]
    fn test_lcp_slides() {
        let text = b"ababcabcabba".into();
        let sa = &sa::naive::<_, usize>(text);
        let isa = &sa.inverse();
        let naive_lcp = naive(text, &sa);

        assert_eq!(*kasai(text, &sa, &isa), *naive_lcp);
        assert_eq!(*phi(text, &sa), *naive_lcp);
    }

    #[test]
    #[ignore = "need to fix handling of first char"]
    fn test_lcp_wikipedia() {
        let text = b"immissiissippi".into();
        let sa = &sa::naive::<_, usize>(text);
        let isa = &sa.inverse();
        let naive_lcp = naive(text, &sa);

        assert_eq!(*kasai(text, &sa, &isa), *naive_lcp);
        assert_eq!(*phi(text, &sa), *naive_lcp);
    }
}
