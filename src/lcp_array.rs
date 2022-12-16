use std::iter::zip;
use std::mem::MaybeUninit;

use crate::index::{ArrayIndex, ToIndex};
use crate::suffix_array::{InverseSuffixArray, SuffixArray};
use crate::text::Text;

/// Represents an owned longest common prefix (LCP) array for a text.
/// Additionally stores a reference to a suffix array of the original text.
///
/// # Invariants
///
/// This type guarantees the following invariants for the LCP array.
///
/// - The LCP array has the same length as the original text.
/// - For any text `LCP[0] == Idx::ZERO`.
/// - TODO
#[derive(Debug, Clone)]
pub struct LCPArray<'sa, 'txt, T, Idx: ArrayIndex> {
    sa: &'sa SuffixArray<'txt, T, Idx>,
    lcp: Box<[Idx]>,
}

#[allow(unused)]
impl<'sa, 'txt, T, Idx: ArrayIndex> LCPArray<'sa, 'txt, T, Idx> {
    /// Returns a reference to the suffix array.
    pub fn sa(&self) -> &'sa SuffixArray<'txt, T, Idx> { self.sa }

    /// Returns a reference to the LCP array.
    pub fn inner(&self) -> &[Idx] { &self.lcp }

    /// Returns the LCP array as a boxed slice.
    pub fn into_inner(self) -> Box<[Idx]> { self.lcp }

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

unsafe fn init_boxed_slice<Idx, Init>(len: usize, init: Init) -> Box<[Idx]>
where
    Init: FnOnce(&mut [MaybeUninit<Idx>]),
    Idx: ArrayIndex,
{
    let mut lcp = Vec::with_capacity(len);
    init(lcp.spare_capacity_mut());
    lcp.set_len(len);
    lcp.into_boxed_slice()
}

/// Constructs an LCP array the given text and suffix array, using the naive algorithm.
///
/// Each element of the LCP array is computed by comparing the two suffixes of
/// the original text. The worst case performance is _O(n²)_, with all-a texts
/// being the worst possible input for the algorithm.
pub fn naive<'sa, 'txt, T: Ord, Idx: ArrayIndex>(
    sa: &'sa SuffixArray<'txt, T, Idx>,
) -> LCPArray<'sa, 'txt, T, Idx> {
    let text = sa.text();

    let mut lcp = Vec::with_capacity(text.len());
    let mut prev = Text::from_slice(&[]);
    for i in sa.inner().iter() {
        let next = &text[*i..];
        lcp.push(prev.common_prefix(next).to_index());
        prev = next;
    }

    LCPArray { lcp: lcp.into_boxed_slice(), sa }
}

/// Constructs an LCP array for the given text and suffix array, using the
/// algorithm developed by Kasai, et. al.
/// TODO citation
///
/// The algorithms works in linear
pub fn kasai<'sa, 'txt, T: Ord, Idx: ArrayIndex>(
    isa: &InverseSuffixArray<'sa, 'txt, T, Idx>,
) -> LCPArray<'sa, 'txt, T, Idx> {
    let (text, sa) = (isa.sa().text(), isa.sa().inner());

    let init = |lcp: &mut [MaybeUninit<Idx>]| {
        isa.inner().iter().enumerate().fold(0, |mut l, (i, &isa_i)| {
            if isa_i != Idx::ZERO {
                let j = sa[isa_i.as_() - 1];
                let suffix_i_l = &text[i + l..];
                let suffix_j_l = &text[j.as_() + l..];
                l += suffix_i_l.common_prefix(suffix_j_l);

                lcp[isa_i.as_()].write(l.to_index());
                l.saturating_sub(1)
            } else {
                l
            }
        });
    };

    let lcp = unsafe { init_boxed_slice(text.len(), init) };
    LCPArray { lcp, sa: isa.sa() }
}

/// TODO
pub fn phi<'sa, 'txt, T: Ord, Idx: ArrayIndex>(
    sa: &'sa SuffixArray<'txt, T, Idx>,
) -> LCPArray<'sa, 'txt, T, Idx> {
    fn phi<Idx: ArrayIndex>(sa: &[Idx]) -> Box<[Idx]> {
        let mut phi = vec![Idx::ZERO; sa.len()];
        for (i, &sa_i) in sa.iter().enumerate().skip(1) {
            phi[sa_i.as_()] = sa[i - 1];
        }

        phi.into_boxed_slice()
    }

    let (text, mut phi) = (sa.text(), phi(sa.inner()));
    phi.iter_mut().enumerate().fold(0, |l, (i, j)| {
        let suffix_i_l = &text[i + l..];
        let suffix_j_l = &text[j.as_() + l..];

        *j = (l + suffix_i_l.common_prefix(suffix_j_l)).to_index();
        j.as_().saturating_sub(1)
    });

    let lcp = sa.inner().iter().map(|&sa_i| phi[sa_i.as_()]).collect();
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
