//! Types and functionality for the construction of LCP arrays.

use std::fmt;
use std::iter::zip;

use crate::prelude::*;
use crate::suffix_array::{InverseSuffixArray, SuffixArray};


/// Represents an owned longest common prefix (LCP) array for a text.
/// Additionally stores a reference to a suffix array of the original text.
///
/// # Invariants
///
/// This type guarantees the following invariants for the LCP array.
///
/// - The LCP array has the same length as the original text.
/// - For `i = 0`: `lcp[i] == 0`.
/// - For `i > 0`: `lcp[i] = max { l | text[sa[i]..sa[i] + l] ==
///                                    text[sa[i-1]..sa[i-1] + l]}`
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
        let (text, mut prev) = (self.sa().text(), &[][..]);
        for (lcp, i) in zip(self.lcp.iter(), self.sa().inner().iter()) {
            assert_eq!(common_prefix(prev, &text[i.as_()..]), lcp.as_());
            prev = &text[i.as_()..];
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
    let mut lcp = vec![zero(); text.len()].into_boxed_slice();

    zip(sa.inner(), &mut *lcp).fold(&[][..], |prev, (i, dst)| {
        let next = &text[i.as_()..];
        *dst = common_prefix(prev, next).to_index();
        next
    });

    LCPArray { lcp, sa }
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
    let mut lcp = vec![zero(); text.len()].into_boxed_slice();

    isa.inner().iter().enumerate().fold(0, |mut l, (i, &isa_i)| {
        if isa_i != zero() {
            let j = sa[isa_i.as_() - 1].as_();
            let suffix_i_l = &text[i + l..];
            let suffix_j_l = &text[j + l..];
            l += common_prefix(suffix_i_l, suffix_j_l);

            lcp[isa_i.as_()] = l.to_index();
            l.saturating_sub(1)
        } else {
            l
        }
    });

    LCPArray { lcp, sa: isa.sa() }
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
        let mut phi = vec![zero(); sa.len()];
        for (i, &sa_i) in sa.iter().enumerate().skip(1) {
            phi[sa_i.as_()] = sa[i - 1];
        }
        phi.into_boxed_slice()
    }

    let (text, mut phi) = (sa.text(), phi(sa.inner()));
    phi.iter_mut().enumerate().fold(0, |l, (i, j)| {
        let suffix_i_l = &text[i + l..];
        let suffix_j_l = &text[j.as_() + l..];

        *j = (l + common_prefix(suffix_i_l, suffix_j_l)).to_index();
        j.as_().saturating_sub(1)
    });

    let mut lcp: Box<_> = sa.inner().iter().map(|&sa_i| phi[sa_i.as_()]).collect();

    if let [ref mut fst, ..] = *lcp {
        *fst = zero();
    }
    LCPArray { sa, lcp }
}

/// Return the length of the longest common prefix of `lhs` and `rhs`.
fn common_prefix<T: PartialEq>(lhs: &[T], rhs: &[T]) -> usize {
    zip(lhs, rhs).take_while(|(l, r)| l == r).count()
}

#[cfg(test)]
mod test {
    use crate::prelude::*;

    fn test_lcp<'txt, Idx: ArrayIndex>(sa: &sa::SuffixArray<u8, Idx>, lcp: &[Idx]) {
        assert_eq!(*super::naive(&sa).lcp, *lcp);
        assert_eq!(*super::kasai(&sa.inverse()).lcp, *lcp);
        assert_eq!(*super::phi(&sa).lcp, *lcp);
    }

    macro_rules! assert_lcp_eq {
        ($text:expr, [$($idx:ty),*]) => {
            $({
                let sa = sa::naive::<_, $idx>($text).unwrap().1;
                test_lcp::<$idx>(&sa, super::naive(&sa).inner());
            })*
        };
        ($text:expr, $lcp:expr, [$($idx:ty),*]) => {
            $( test_lcp::<$idx>(&sa::naive($text).unwrap().1, $lcp); )*
        };
    }

    #[test]
    fn test_empty_text() {
        assert_lcp_eq!(b"", &[], [u8, i8, u16, i16, u32, i32, u64, i64, usize, isize]);
    }

    #[test]
    fn test_simple_text() {
        assert_lcp_eq!(
            b"banana",
            &[0, 1, 3, 0, 0, 2],
            [u8, i8, u16, i16, u32, i32, u64, i64, usize, isize]
        );
    }

    #[test]
    fn test_lcp_slides_with_sentinel() {
        assert_lcp_eq!(
            b"ababcabcabba\0",
            &[0, 0, 1, 2, 2, 5, 0, 2, 1, 1, 4, 0, 3],
            [u8, i8, u16, i16, u32, i32, u64, i64, usize, isize]
        );
    }

    #[test]
    fn test_lcp_slides_no_sentinel() {
        assert_lcp_eq!(
            b"ababcabcabba",
            &[0, 1, 2, 2, 5, 0, 2, 1, 1, 4, 0, 3],
            [u8, i8, u16, i16, u32, i32, u64, i64, usize, isize]
        );
    }

    #[test]
    fn test_lcp_wikipedia_with_sentinel() {
        assert_lcp_eq!(
            b"immissiissippi\0",
            &[0, 0, 1, 1, 1, 1, 4, 0, 1, 0, 1, 0, 2, 1, 3],
            [u8, i8, u16, i16, u32, i32, u64, i64, usize, isize]
        );
    }

    #[test]
    fn test_lcp_wikipedia_no_sentinel() {
        assert_lcp_eq!(
            b"immissiissippi",
            &[0, 1, 1, 1, 1, 4, 0, 1, 0, 1, 0, 2, 1, 3],
            [u8, i8, u16, i16, u32, i32, u64, i64, usize, isize]
        );
    }

    #[test]
    fn test_lcp_lorem_ipsum() {
        assert_lcp_eq!(
            b"Lorem ipsum dolor sit amet, qui minim labore adipisicing \
            minim sint cillum sint consectetur cupidatat.",
            [u8, i8, u16, i16, u32, i32, u64, i64, usize, isize]
        );
    }

    #[test]
    fn test_lcp_lorem_ipsum_long() {
        assert_lcp_eq!(
            b"Lorem ipsum dolor sit amet, officia \
            excepteur ex fugiat reprehenderit enim labore culpa sint ad nisi Lorem \
            pariatur mollit ex esse exercitation amet. Nisi anim cupidatat \
            excepteur officia. Reprehenderit nostrud nostrud ipsum Lorem est \
            aliquip amet voluptate voluptate dolor minim nulla est proident. \
            Nostrud officia pariatur ut officia. Sit irure elit esse ea nulla sunt \
            ex occaecat reprehenderit commodo officia dolor Lorem duis laboris \
            cupidatat officia voluptate. Culpa proident adipisicing id nulla nisi \
            laboris ex in Lorem sunt duis officia eiusmod. Aliqua reprehenderit \
            commodo ex non excepteur duis sunt velit enim. Voluptate laboris sint \
            cupidatat ullamco ut ea consectetur et est culpa et culpa duis.",
            [u16, i16, u32, i32, u64, i64, usize, isize]
        );
    }
}
