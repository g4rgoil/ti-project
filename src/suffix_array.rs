use std::fmt;
use std::iter::zip;

pub use alphabet::Alphabet;

use self::alphabet::Symbol;
use crate::cast::Transmutable;
use crate::prelude::*;
use crate::sais;

pub type SAResult<'a, T, Idx> = Result<(usize, SuffixArray<'a, T, Idx>), Error>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The text of size `len` does not fit the specified index type with
    /// capacity `cap`.
    IndexTooSmall { len: usize, cap: usize },
}

/// Computes the suffix array for `text` using the naive algorithm.
///
/// The implementation uses [`sort_by_key`] from the standard library.
/// Comparing two suffixes takes _O(n)_ time, therefore the worst case
/// performance of the algorithm is _O(n² * log(n))_.
///
/// The suffix array will use indices of type `Idx`. If the index is too
/// _small_ for the given text, `Err(_)` is returned.
///
/// [`sort_by_key`]: slice::sort_by_key
pub fn naive<T: Symbol, Idx: ArrayIndex>(text: &[T]) -> SAResult<T, Idx> {
    if text.len().saturating_sub(1) <= Idx::MAX.as_() {
        let mut sa: Box<_> = (0..text.len()).map(Idx::from_usize).collect();
        sa.sort_unstable_by_key(|i| &text[i.as_()..]);

        let memory = sa.len() * std::mem::size_of::<Idx>();
        Ok((memory, SuffixArray { text, sa }))
    } else {
        let (len, cap) = (text.len(), Idx::MAX.as_().saturating_add(1));
        Err(Error::IndexTooSmall { len, cap })
    }
}

/// Computes the suffix array for `text` using Suffix Array Induced Sorting (SAIS).
///
/// The suffix array will use indices of type `Idx`. The index must have a
/// corresponding signed type as defined by [`IntTypes`]. The maxiumum allowable
/// length for `text` is defined by the signed index type.
pub fn sais<Idx>(text: &[u8]) -> SAResult<u8, Idx>
where
    Idx: ArrayIndex + IntTypes + Transmutable<Idx::Signed>,
    Idx::Signed: ArrayIndex,
{
    sais::sais(text)
}

/// Represents an owned suffix array for a text. Additionally stores a reference
/// to the original text.
///
/// # Invariants
///
/// This type guarantees the following invariants for the suffix array.
///
/// - The suffix array has the same length as the original text.
/// - The suffix array is a permutation of `[0..len)`, where `len` is the length
///   of the original text.
/// - The suffix array sorts the suffixes of the original text in ascending
///   lexicographic order.
pub struct SuffixArray<'txt, T, Idx> {
    text: &'txt [T],
    sa: Box<[Idx]>,
}

impl<'txt, T, Idx> SuffixArray<'txt, T, Idx> {
    /// Creates a suffix array for `text` using `sa`.
    ///
    /// # Safety
    /// The caller must ensure that `sa` upholds all invariants of a suffix array.
    pub unsafe fn new_unchecked(text: &'txt [T], sa: Box<[Idx]>) -> Self {
        debug_assert_eq!(text.len(), sa.len());
        Self { text, sa }
    }

    /// Returns a reference to the original text.
    pub fn text(&self) -> &'txt [T] { self.text }

    /// Returns a reference to the suffix array.
    pub fn inner(&self) -> &[Idx] { &self.sa }

    /// Returns the suffix array as a boxed slice.
    pub fn into_inner(self) -> Box<[Idx]> { self.sa }

    /// Returns the inverse of the suffix array.
    pub fn inverse(&self) -> InverseSuffixArray<'txt, '_, T, Idx>
    where
        Idx: ArrayIndex,
    {
        let mut isa = vec![zero(); self.sa.len()].into_boxed_slice();

        for (i, sa_i) in self.sa.iter().enumerate() {
            // SAFETY: Because a SuffixArray is a permutation of (0, len),
            // sa_i is guaranteed to not be out of bounds for isa
            unsafe { *isa.get_unchecked_mut(sa_i.as_()) = i.to_index() };
        }

        InverseSuffixArray { sa: self, isa }
    }

    /// Ensures that the suffix array upholds the required invariants, and
    /// panics if it does not.
    ///
    /// Note: This is a **very expensive** operation, with _O(n²)_ worst case
    /// performance.
    pub fn verify(&self, text: &[T])
    where
        Idx: ArrayIndex,
        T: Ord + fmt::Debug,
    {
        let is_increasing = zip(self.sa.iter(), self.sa.iter().skip(1))
            .all(|(i, j)| text[i.as_()..] < text[j.as_()..]);
        assert!(is_increasing, "the suffix array is not sorted in increasing order");

        let mut arr = vec![false; text.len()];
        self.sa.iter().for_each(|i| arr[i.as_()] = true);
        assert!(
            arr.iter().all(|b| *b),
            "the suffix array is not a permutation of [0..len)"
        );
    }
}

impl<'txt, T, Idx: Clone> Clone for SuffixArray<'txt, T, Idx> {
    fn clone(&self) -> Self { Self { text: self.text(), sa: self.sa.clone() } }
}

impl<'txt, T: fmt::Debug, Idx: fmt::Debug> fmt::Debug for SuffixArray<'txt, T, Idx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SuffixArray")
            .field("text", &self.text())
            .field("sa", &self.inner())
            .finish()
    }
}

/// Represents an inverse suffix array for a text. Additionally stores a
/// reference to a suffix array of the original text.
///
/// # Invariants.
///
/// This type guarantees the following invariants for the inverse suffix array.
///
/// - The inverse suffix array has the same length as the original text.
/// - The inverse suffix array is a permutation of `[0..len)`, where `len` is
///   the length of the original text.
pub struct InverseSuffixArray<'sa, 'txt, T, Idx> {
    sa: &'sa SuffixArray<'txt, T, Idx>,
    isa: Box<[Idx]>,
}

impl<'sa, 'txt, T, Idx> InverseSuffixArray<'sa, 'txt, T, Idx> {
    /// Returns a reference to the suffix array of the original text.
    pub fn sa(&self) -> &'sa SuffixArray<'txt, T, Idx> { self.sa }

    /// Returns a reference to the inverse suffix array.
    pub fn inner(&self) -> &[Idx] { &self.isa }

    /// Returns the inverse suffix array as a boxed slice.
    pub fn into_inner(self) -> Box<[Idx]> { self.isa }
}

impl<'sa, 'txt, T, Idx: Clone> Clone for InverseSuffixArray<'sa, 'txt, T, Idx> {
    fn clone(&self) -> Self { Self { sa: self.sa(), isa: self.isa.clone() } }
}

impl<'sa, 'txt, T: fmt::Debug, Idx: fmt::Debug> fmt::Debug
    for InverseSuffixArray<'sa, 'txt, T, Idx>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InverseSuffixArray")
            .field("text", &self.sa().text())
            .field("sa", &self.sa().inner())
            .field("isa", &self.inner())
            .finish()
    }
}

pub mod alphabet {
    use std::{fmt, marker::PhantomData};

    use crate::index::*;
    use crate::num::*;

    pub trait Symbol: Sized + Copy + Ord + AsPrimitive<usize> + fmt::Debug {}

    impl<T: PrimInt + AsPrimitive<usize>> Symbol for T {}

    pub trait Alphabet: Copy {
        type Symbol: Symbol;

        fn size(&self) -> usize;
    }

    #[derive(Debug, Clone, Copy)]
    pub struct ByteAlphabet;

    impl Alphabet for ByteAlphabet {
        type Symbol = u8;

        fn size(&self) -> usize { u8::MAX as usize + 1 }
    }

    #[derive(Debug, Clone, Copy)]
    pub struct IndexAlphabet<Idx> {
        size: usize,
        _phantom: PhantomData<Idx>,
    }

    impl<Idx: ArrayIndex> IndexAlphabet<Idx> {
        pub fn new(size: usize) -> Self { Self { size, _phantom: PhantomData } }
    }

    impl<Idx: Symbol> Alphabet for IndexAlphabet<Idx> {
        type Symbol = Idx;

        fn size(&self) -> usize { self.size }
    }
}
