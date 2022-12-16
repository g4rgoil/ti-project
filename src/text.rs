use std::{borrow, ops, slice};

use crate::index::ArrayIndex;

/// A dynamically sized view into a text used for text indexing algorithms.
///
/// Wraps around a slice to provided the necessary operations for the
/// convenient construction of suffix and LCP arrays.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Text<T>(pub [T]);

impl<T> Text<T> {
    /// Create a reference to a text from a reference to a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// let text = Text::from_slice(b"Hello world!");
    /// assert_eq!(text[0], b'H');
    /// ```
    pub fn from_slice(slice: &[T]) -> &Self {
        // Safety: Text has same internal representation as [T]. The resulting
        // pointer can be safely dereferenced, because it comes from a reference.
        // The lifetime of the returned reference is bound by that of `slice`.
        unsafe { &*(slice as *const [T] as *const Text<T>) }
    }

    /// Returns the number of elements in the text.
    ///
    /// # Examples
    ///
    /// ```
    /// let text = Text::from_slice(b"foo");
    /// assert_eq!(text.len(), 3);
    /// ```
    pub fn len(&self) -> usize { self.0.len() }

    /// Returns `true` if the text is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// let text = Text::from_slice(b"foo");
    /// assert_eq!(text.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool { self.0.is_empty() }

    /// Returns `true` if the text can be indexed using `Idx`.
    ///
    /// # Examples
    ///
    /// ```
    /// let text = Text::from_slice(&[0; 420]);
    /// assert_eq!(text.fits_index::<u8>, false);
    /// assert_eq!(text.fits_index::<u16>, true);
    /// ```
    pub fn fits_index<Idx: ArrayIndex>(&self) -> bool { self.len() <= Idx::MAX.as_() }

    /// Returns an iterator over the elements of the text.
    ///
    /// # Examples
    ///
    /// ```
    /// let text = Text::from_slice(b"foo");
    /// let mut iter = text.iter();
    ///
    /// assert_eq!(iter.next(), Some(b'f'));
    /// assert_eq!(iter.next(), Some(b'o'));
    /// assert_eq!(iter.next(), Some(b'o'));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> slice::Iter<T> { self.into_iter() }

    /// Returns the length of the longest common prefix of `self` and `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// let lhs = Text::from_slice(b"abcabcabba");
    /// let rhs = Text::from_slice(b"abcabba");
    /// assert_eq!(lhs.common_prefix(rhs), 5);
    /// ```
    pub fn common_prefix(&self, other: &Text<T>) -> usize
    where
        T: PartialEq,
    {
        self.iter().zip(other).take_while(|(l, r)| l == r).count()
    }
}

impl<T> Default for &Text<T> {
    fn default() -> Self { Text::from_slice(&[]) }
}

impl<'a, T> From<&'a [T]> for &'a Text<T> {
    fn from(value: &'a [T]) -> Self { Text::from_slice(value) }
}

impl<'a, T> From<&'a Text<T>> for &'a [T] {
    fn from(value: &'a Text<T>) -> Self { &value.0 }
}

impl<'a, T, const N: usize> From<&'a [T; N]> for &'a Text<T> {
    fn from(value: &'a [T; N]) -> Self { Text::from_slice(value) }
}

impl<T> AsRef<[T]> for Text<T> {
    fn as_ref(&self) -> &[T] { self.into() }
}

impl<T> borrow::Borrow<[T]> for Text<T> {
    fn borrow(&self) -> &[T] { self.into() }
}

impl<'a, T> IntoIterator for &'a Text<T> {
    type IntoIter = slice::Iter<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> Self::IntoIter { self.0.iter() }
}

impl<I: TextIndex<T>, T> ops::Index<I> for Text<T> {
    type Output = I::Output;

    fn index(&self, index: I) -> &Self::Output { index.index(self) }
}

/// A helper trait used to index texts (cf. [`std::slice::SliceIndex`]).
pub trait TextIndex<T> {
    /// The output type returned by [`TextIndex::index`].
    type Output: ?Sized;

    /// Returns a shared reference to the output at the given location.
    fn index(self, text: &Text<T>) -> &Self::Output;
}

impl<T, Idx: ArrayIndex> TextIndex<T> for Idx {
    type Output = T;

    fn index(self, text: &Text<T>) -> &Self::Output { &text.0[self.as_()] }
}

impl<T, Idx: ArrayIndex> TextIndex<T> for ops::Range<Idx> {
    type Output = Text<T>;

    fn index(self, text: &Text<T>) -> &Self::Output {
        Text::from_slice(&text.0[self.start.as_()..self.end.as_()])
    }
}

impl<T, Idx: ArrayIndex> TextIndex<T> for ops::RangeFrom<Idx> {
    type Output = Text<T>;

    fn index(self, text: &Text<T>) -> &Self::Output {
        Text::from_slice(&text.0[self.start.as_()..])
    }
}

impl<T> TextIndex<T> for ops::RangeFull {
    type Output = Text<T>;

    fn index(self, text: &Text<T>) -> &Self::Output { Text::from_slice(&text.0[..]) }
}

impl<T, Idx: ArrayIndex> TextIndex<T> for ops::RangeInclusive<Idx> {
    type Output = Text<T>;

    fn index(self, text: &Text<T>) -> &Self::Output {
        Text::from_slice(&text.0[self.start().as_()..=self.end().as_()])
    }
}

impl<T, Idx: ArrayIndex> TextIndex<T> for ops::RangeTo<Idx> {
    type Output = Text<T>;

    fn index(self, text: &Text<T>) -> &Self::Output {
        Text::from_slice(&text.0[..self.end.as_()])
    }
}

impl<T, Idx: ArrayIndex> TextIndex<T> for ops::RangeToInclusive<Idx> {
    type Output = Text<T>;

    fn index(self, text: &Text<T>) -> &Self::Output {
        Text::from_slice(&text.0[..=self.end.as_()])
    }
}
