use std::fmt::{self, Debug};
use std::iter::zip;

use self::result::MemoryResult;
use crate::num::{ArrayIndex, AsPrimitive, Limits, ToIndex, Zero};
use crate::sais;
use crate::sais::index::SignedIndex;
use crate::text::Text;

pub type Result<'txt, T, Idx> =
    std::result::Result<MemoryResult<SuffixArray<'txt, T, Idx>>, Error>;

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
/// [`sort_by_key`]: slice::sort_by_key
pub fn naive<T: Symbol, Idx: ArrayIndex>(text: &Text<T>) -> Result<T, Idx> {
    // TODO put this into its own function
    if text.len().saturating_sub(1) <= Idx::MAX.as_() {
        let mut sa: Box<_> = (0..text.len()).map(Idx::from_usize).collect();
        sa.sort_unstable_by_key(|i| &text[*i..]);

        // TODO don't count suffix array?!
        let mut builder = MemoryResult::builder();
        builder.add_values::<T>(text.len());
        Ok(builder.build(SuffixArray { text, sa }))
    } else {
        let (len, cap) = (text.len(), Idx::MAX.as_().saturating_add(1));
        Err(Error::IndexTooSmall { len, cap })
    }
}

/// Computes the suffix array for `text` using Suffix-Array-Induced-Sorting (SAIS).
///
/// TODO
pub fn sais<Idx: sais::index::Index>(text: &Text<u8>) -> Result<u8, Idx>
where
    Idx::Signed: SignedIndex,
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
    text: &'txt Text<T>,
    sa: Box<[Idx]>,
}

impl<'txt, T, Idx> SuffixArray<'txt, T, Idx> {
    pub unsafe fn new_unchecked(text: &'txt Text<T>, sa: Box<[Idx]>) -> Self {
        // TODO debug asserts?
        Self { text, sa }
    }

    /// Returns a reference to the original text.
    pub fn text(&self) -> &'txt Text<T> { self.text }

    /// Returns a reference to the suffix array.
    pub fn inner(&self) -> &[Idx] { &self.sa }

    /// Returns the suffix array as a boxed slice.
    pub fn into_inner(self) -> Box<[Idx]> { self.sa }

    /// Returns the inverse of the suffix array.
    pub fn inverse(&self) -> InverseSuffixArray<'txt, '_, T, Idx>
    where
        Idx: ArrayIndex,
    {
        // TODO use MaybeUninit for optimization

        let mut isa = vec![Idx::ZERO; self.sa.len()];

        for (i, sa_i) in self.sa.iter().enumerate() {
            // SAFETY: Because a SuffixArray is a permutation of (0, len),
            // sa_i is guaranteed to not be out of bounds for isa
            unsafe { *isa.get_unchecked_mut(sa_i.as_()) = i.to_index() };
        }

        InverseSuffixArray { sa: self, isa: isa.into_boxed_slice() }
    }

    /// Ensures that the suffix array upholds the required invariants, and
    /// panics if it does not.
    ///
    /// Note: This is a **very expensive** operation, with _O(n²)_ worst case
    /// performance.
    pub fn verify(&self, text: &Text<T>)
    where
        Idx: ArrayIndex,
        T: Ord + Debug,
    {
        let is_increasing = zip(self.sa.iter(), self.sa.iter().skip(1))
            .all(|(i, j)| text[*i..] < text[*j..]);
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

// TODO actually use this trait for sa impls
// TODO what about signed types?
pub trait Symbol:
    Sized + Copy + Ord + Debug + Zero + Limits + AsPrimitive<usize>
{
}

#[doc(hidden)]
macro_rules! impl_symbol {
    ( $( $type:ty ),* ) => {
        $( impl Symbol for $type {} )*
    };
}

impl_symbol!(u8, u16, u32, u64, usize);


pub mod result {
    #[derive(Debug, Clone, Copy)]
    #[must_use]
    pub struct MemoryResult<T> {
        pub value: T,
        pub memory: usize,
    }

    impl<T> MemoryResult<T> {
        pub fn builder() -> Builder<T> {
            Builder { memory: 0, _phantom: Default::default() }
        }

        pub fn add_to<S>(self, builder: &mut Builder<S>) -> T {
            builder.memory += self.memory;
            self.value
        }
    }

    #[derive(Debug, Clone, Copy)]
    pub struct Builder<T> {
        pub memory: usize,
        _phantom: std::marker::PhantomData<T>,
    }

    impl<T> Builder<T> {
        pub fn build(self, value: T) -> MemoryResult<T> {
            MemoryResult { value, memory: self.memory }
        }

        pub fn add_values<S>(&mut self, num: usize) {
            self.memory += num * std::mem::size_of::<S>();
        }
    }
}
