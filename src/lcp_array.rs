use std::fmt;
use std::iter::zip;

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
pub struct LCPArray<'sa, 'txt, T, Idx> {
    sa: &'sa SuffixArray<'txt, T, Idx>,
    lcp: Box<[Idx]>,
}

impl<'sa, 'txt, T, Idx> LCPArray<'sa, 'txt, T, Idx> {
    /// Returns a reference to the suffix array.
    pub fn sa(&self) -> &'sa SuffixArray<'txt, T, Idx> { self.sa }

    /// Returns a reference to the LCP array.
    pub fn inner(&self) -> &[Idx] { &self.lcp }

    /// Returns the LCP array as a boxed slice.
    pub fn into_inner(self) -> Box<[Idx]> { self.lcp }

    /// Ensures that the LCP array upholds the required invariants, and panics
    /// if it does not.
    ///
    /// Note: This is a **very expensive** operation, with _O(n²)_ worst case
    /// performance.
    pub fn verify(&self)
    where
        Idx: ArrayIndex,
        T: PartialEq,
    {
        let (text, mut prev) = (self.sa().text(), Text::from_slice(&[]));
        for (lcp, i) in zip(self.lcp.iter(), self.sa().inner().iter()) {
            assert_eq!(prev.common_prefix(&text[*i..]), lcp.as_());
            prev = &text[*i..];
        }
    }
}

impl<'sa, 'txt, T, Idx: Clone> Clone for LCPArray<'sa, 'txt, T, Idx> {
    fn clone(&self) -> Self { Self { sa: self.sa(), lcp: self.lcp.clone() } }
}

impl<'sa, 'txt, T: fmt::Debug, Idx: fmt::Debug> fmt::Debug
    for LCPArray<'sa, 'txt, T, Idx>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LCPArray")
            .field("text", &self.sa().text())
            .field("sa", &self.sa().inner())
            .field("lcp", &self.inner())
            .finish()
    }
}

/// Constructs an LCP array for the given text and suffix array using the naive
/// algorithm.
///
/// Each element of the LCP array is computed by comparing the two suffixes of
/// the original text. The worst case performance is _O(n²)_, with all-a texts
/// being the worst possible input for the algorithm.
pub fn naive<'sa, 'txt, T: Ord, Idx: ArrayIndex>(
    sa: &'sa SuffixArray<'txt, T, Idx>,
) -> LCPArray<'sa, 'txt, T, Idx> {
    let text = sa.text();
    let mut lcp = vec![Idx::ZERO; text.len()];

    let iter = zip(sa.inner().iter(), lcp.iter_mut());
    iter.fold(Text::from_slice(&[]), |prev, (i, dst)| {
        let next = &text[*i..];
        *dst = prev.common_prefix(next).to_index();
        next
    });

    LCPArray { lcp: lcp.into_boxed_slice(), sa }
}

/// Constructs an LCP array for the given text and suffix array using the
/// linear-time algorithm developed by Kasai, et al. \[1\].
///
/// # References
///
/// \[1\] Kasai, T., Lee, G., Arimura, H., Arikawa, S., Park, K. (2001).
/// _Linear-Time Longest-Common-Prefix Computation in Suffix Arrays and Its
/// Applications._ DOI: [10.1007/3-540-48194-X_17]
///
/// [10.1007/3-540-48194-X_17]: https://doi.org/10.1007/3-540-48194-X_17
pub fn kasai<'sa, 'txt, T: Ord, Idx: ArrayIndex>(
    isa: &InverseSuffixArray<'sa, 'txt, T, Idx>,
) -> LCPArray<'sa, 'txt, T, Idx> {
    let (text, sa) = (isa.sa().text(), isa.sa().inner());
    let mut lcp = Vec::with_capacity(text.len());
    {
        let lcp = lcp.spare_capacity_mut();
        let iter = isa.inner().iter().enumerate();
        iter.fold(0, |mut l, (i, &isa_i)| {
            if isa_i != Idx::ZERO {
                let j = sa[isa_i.as_() - 1];
                let suffix_i_l = &text[i + l..];
                let suffix_j_l = &text[j.as_() + l..];
                l += suffix_i_l.common_prefix(suffix_j_l);

                lcp[isa_i.as_()].write(l.to_index());
                l.saturating_sub(1)
            } else {
                lcp[isa_i.as_()].write(Idx::ZERO);
                l
            }
        });
    }

    unsafe { lcp.set_len(text.len()) };
    LCPArray { lcp: lcp.into_boxed_slice(), sa: isa.sa() }
}

/// Constructs an LCP array for the given text and suffix array using the
/// liner time algorithm developed by Kärkkäinen et al. \[1\].
///
/// The algorithm works by first constructing the ɸ-array (hence the name of
/// the algorithm). The ɸ-array is used to construct the _permuted_ LCP (PLCP)
/// array, which is subsequently used to construct the LCP array.
///
/// # References
///
/// \[1\] Kärkkäinen, J., Manzini, G., Puglisi, S.J. (2009).
/// _Permuted Longest-Common-Prefix Array._
/// In: Kucherov, G., Ukkonen, E. (eds) _Combinatorial Pattern Matching._
/// DOI: [10.1007/978-3-642-02441-2_17]
///
/// [10.1007/978-3-642-02441-2_17]: https://doi.org/10.1007/978-3-642-02441-2_17
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

    let mut lcp: Box<_> = sa.inner().iter().map(|&sa_i| phi[sa_i.as_()]).collect();

    // TODO is there a better way?
    if let Some(fst) = lcp.first_mut() {
        *fst = Idx::ZERO;
    }
    LCPArray { sa, lcp }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::suffix_array as sa;

    #[test]
    fn test_empty_text() {
        let text = b"".into();
        let sa = sa::naive::<_, usize>(text);
        let isa = sa.inverse();

        assert_eq!(*naive(&sa).lcp, []);
        assert_eq!(*kasai(&isa).lcp, []);
        assert_eq!(*phi(&sa).lcp, []);
    }

    #[test]
    fn test_simple_text() {
        let text = b"banana".into();
        let sa = sa::naive::<_, usize>(text);
        let isa = sa.inverse();
        let lcp = [0, 1, 3, 0, 0, 2];

        assert_eq!(*naive(&sa).lcp, lcp);
        assert_eq!(*kasai(&isa).lcp, lcp);
        assert_eq!(*phi(&sa).lcp, lcp);
    }
    #[test]
    fn test_lcp_slides_with_sentinel() {
        let text = b"ababcabcabba\0".into();
        let sa = sa::naive::<_, usize>(text);
        let isa = sa.inverse();
        let lcp = [0, 0, 1, 2, 2, 5, 0, 2, 1, 1, 4, 0, 3];

        assert_eq!(*naive(&sa).lcp, lcp);
        assert_eq!(*kasai(&isa).lcp, lcp);
        assert_eq!(*phi(&sa).lcp, lcp);
    }

    #[test]
    fn test_lcp_slides_no_sentinel() {
        let text = b"ababcabcabba".into();
        let sa = sa::naive::<_, usize>(text);
        let isa = sa.inverse();
        let lcp = [0, 1, 2, 2, 5, 0, 2, 1, 1, 4, 0, 3];

        assert_eq!(*naive(&sa).lcp, lcp);
        assert_eq!(*kasai(&isa).lcp, lcp);
        assert_eq!(*phi(&sa).lcp, lcp);
    }

    #[test]
    fn test_lcp_wikipedia_with_sentinel() {
        let text = b"immissiissippi\0".into();
        let sa = sa::naive::<_, usize>(text);
        let isa = sa.inverse();
        let lcp = [0, 0, 1, 1, 1, 1, 4, 0, 1, 0, 1, 0, 2, 1, 3];

        assert_eq!(*naive(&sa).lcp, lcp);
        assert_eq!(*kasai(&isa).lcp, lcp);
        assert_eq!(*phi(&sa).lcp, lcp);
    }

    #[test]
    fn test_lcp_wikipedia_no_sentinel() {
        let text = b"immissiissippi".into();
        let sa = sa::naive::<_, usize>(text);
        let isa = sa.inverse();
        let lcp = [0, 1, 1, 1, 1, 4, 0, 1, 0, 1, 0, 2, 1, 3];

        assert_eq!(*naive(&sa).lcp, lcp);
        assert_eq!(*kasai(&isa).lcp, lcp);
        assert_eq!(*phi(&sa).lcp, lcp);
    }
}
