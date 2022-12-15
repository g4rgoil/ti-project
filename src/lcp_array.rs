use std::iter::zip;

use crate::index::{ArrayIndex, ToIndex};
use crate::suffix_array::{InverseSuffixArray, SuffixArray};
use crate::text::Text;

#[derive(Debug, Clone)]
pub struct LCPArray<'sa, 'txt, T, Idx: ArrayIndex> {
    #[allow(unused)]
    sa: &'sa SuffixArray<'txt, T, Idx>,
    lcp: Box<[Idx]>,
}

#[allow(unused)]
impl<'sa, 'txt, T, Idx: ArrayIndex> LCPArray<'sa, 'txt, T, Idx> {
    pub fn sa(&self) -> &'sa SuffixArray<T, Idx> { self.sa }

    pub fn inner(&self) -> &[Idx] { &self.lcp }

    pub fn verify(&self)
    where
        T: PartialEq,
    {
        let (text, mut prev) = (self.sa().text(), Text::from_slice(&[]));
        for (lcp, i) in zip(self.lcp.iter(), self.sa().inner().iter()) {
            assert_eq!(prev.common_prefix(&text[*i..]), lcp.as_());
            prev = &text[*i..];
        }
    }
}


pub fn naive<'sa, 'txt, T: Ord, Idx: ArrayIndex>(
    sa: &'sa SuffixArray<'txt, T, Idx>,
) -> LCPArray<'sa, 'txt, T, Idx> {
    let text = sa.text();
    let mut lcp = Vec::with_capacity(text.len());

    // TODO this is bad
    let mut prev = Text::from_slice(&[]);
    for i in sa.inner().iter() {
        let next = &text[*i..];
        lcp.push(prev.common_prefix(next).to_index());
        prev = next;
    }

    LCPArray { lcp: lcp.into_boxed_slice(), sa }
}

pub fn kasai<'sa, 'txt, T: Ord, Idx: ArrayIndex>(
    isa: &InverseSuffixArray<'sa, 'txt, T, Idx>,
) -> LCPArray<'sa, 'txt, T, Idx> {
    let (text, sa) = (isa.sa().text(), isa.sa().inner());
    let mut lcp = vec![Idx::ZERO; text.len()];

    let mut l = 0;
    for (i, &isa_i) in isa.inner().iter().enumerate() {
        if isa_i != Idx::ZERO {
            let j = sa[isa_i.as_() - 1];
            let suffix_i_l = &text[i + l..];
            let suffix_j_l = &text[j.as_() + l..];
            l += suffix_i_l.common_prefix(suffix_j_l);

            lcp[isa_i.as_()] = l.to_index();
            l = l.saturating_sub(1);
        }
    }

    LCPArray { lcp: lcp.into_boxed_slice(), sa: isa.sa() }
}

pub fn phi<'sa, 'txt, T: Ord, Idx: ArrayIndex>(
    sa: &'sa SuffixArray<'txt, T, Idx>,
) -> LCPArray<'sa, 'txt, T, Idx> {
    // TODO use MaybeUninit for optimization

    let lcp = {
        let (text, sa) = (sa.text(), sa.inner());
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

        sa.iter().map(|&sa_i| phi[sa_i.as_()]).collect()
    };

    LCPArray { sa, lcp }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::suffix_array as sa;

    // TODO need more tests here
    // TODO need verify() like for SA

    #[test]
    fn test_empty_text() {
        let text = b"".into();
        let sa = &sa::naive::<_, usize>(text);
        let isa = &sa.inverse();

        assert_eq!(*naive(sa).lcp, []);
        assert_eq!(*kasai(isa).lcp, []);
        assert_eq!(*phi(sa).lcp, []);
    }

    #[test]
    fn test_simple_text() {
        let text = b"banana".into();
        let sa = &sa::naive::<_, usize>(text);
        let isa = &sa.inverse();
        let lcp = [0, 1, 3, 0, 0, 2];

        assert_eq!(*naive(&sa).lcp, lcp);
        assert_eq!(*kasai(&isa).lcp, lcp);
        assert_eq!(*phi(&sa).lcp, lcp);
    }

    #[test]
    #[ignore = "need to fix handling of first char"]
    fn test_lcp_slides() {
        let text = b"ababcabcabba".into();
        let sa = &sa::naive::<_, usize>(text);
        let isa = &sa.inverse();
        let naive_lcp = naive(&sa);

        assert_eq!(*kasai(&isa).lcp, *naive_lcp.lcp);
        assert_eq!(*phi(&sa).lcp, *naive_lcp.lcp);
    }

    #[test]
    #[ignore = "need to fix handling of first char"]
    fn test_lcp_wikipedia() {
        let text = b"immissiissippi".into();
        let sa = &sa::naive::<_, usize>(text);
        let isa = &sa.inverse();
        let naive_lcp = naive(&sa);

        assert_eq!(*kasai(&isa).lcp, *naive_lcp.lcp);
        assert_eq!(*phi(&sa).lcp, *naive_lcp.lcp);
    }
}
