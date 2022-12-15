use std::{ops, slice};

use crate::index::ArrayIndex;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct Text<T>(pub [T]);

impl<T> Text<T> {
    pub fn from_slice(slice: &[T]) -> &Self {
        // Safety: Text has same internal representation as [T]. The resulting
        // pointer can be safely dereferenced, because it comes from a reference.
        // The lifetime of the returned reference is bound by that of `slice`.
        unsafe { &*(slice as *const [T] as *const Text<T>) }
    }

    pub fn len(&self) -> usize { self.0.len() }

    pub fn is_empty(&self) -> bool { self.0.is_empty() }

    pub fn fits_index<Idx: ArrayIndex>(&self) -> bool { self.len() <= Idx::MAX.as_() }

    pub fn iter(&self) -> slice::Iter<T> { self.into_iter() }

    pub fn common_prefix(&self, other: &Text<T>) -> usize
    where
        T: PartialEq,
    {
        self.iter().zip(other).take_while(|(l, r)| l == r).count()
    }
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

impl<'a, T> IntoIterator for &'a Text<T> {
    type IntoIter = slice::Iter<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> Self::IntoIter { self.0.iter() }
}

impl<I: TextIndex<T>, T> ops::Index<I> for Text<T> {
    type Output = I::Output;

    fn index(&self, index: I) -> &Self::Output { index.index(self) }
}

pub trait TextIndex<T> {
    type Output: ?Sized;

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
