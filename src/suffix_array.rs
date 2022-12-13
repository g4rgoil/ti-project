mod sais;

use std::fmt::Debug;
use std::ops::{Add, AddAssign, Sub, SubAssign};
use std::{iter::zip, ops::Deref};

use crate::TextExt;

/// TODO: Invariants:
/// - sa is permutation of (0, sa.len())
#[derive(Debug, Clone)]
pub struct SuffixArray<Idx: ArrayIndex = usize>(Box<[Idx]>);

impl<Idx: ArrayIndex> Deref for SuffixArray<Idx> {
    type Target = [Idx];

    fn deref(&self) -> &Self::Target { &self.0 }
}

impl<Idx: ArrayIndex> SuffixArray<Idx> {
    #[inline(never)]
    pub fn inverse(&self) -> InverseSuffixArray {
        // TODO use MaybeUninit for optimization

        let mut isa = vec![0; self.len()];

        for (i, sa_i) in self.iter().enumerate() {
            // SAFETY: Because a SuffixArray is a permutation of (0, len),
            // sa_i is guaranteed to not be out of bounds for isa
            unsafe { *isa.get_unchecked_mut(sa_i.to_usize()) = i };
        }

        InverseSuffixArray(isa.into_boxed_slice())
    }

    // TODO move to test module
    #[allow(unused)]
    pub fn verify<T: Ord + Debug>(&self, text: &[T]) {
        assert!(zip(self.0.iter(), self.0.iter().skip(1)).all(|(i, j)| {
            text.suffix(i.to_usize()) < text.suffix(j.to_usize())
        }));

        let mut arr = vec![false; text.len()];
        self.0.iter().for_each(|i| arr[i.to_usize()] = true);
        assert_eq!(arr, vec![true; text.len()]);
    }
}

/// TODO: Invariants:
/// - sa is permutation of (0, sa.len())
#[derive(Debug, Clone)]
pub struct InverseSuffixArray<Idx: ArrayIndex = usize>(Box<[Idx]>);

impl<Idx: ArrayIndex> Deref for InverseSuffixArray<Idx> {
    type Target = [Idx];

    fn deref(&self) -> &Self::Target { &self.0 }
}

#[allow(unused)]
pub fn naive<T: Ord + Debug, Idx: ArrayIndex>(text: &[T]) -> SuffixArray<Idx> {
    // TODO This should return a result instead
    assert!(fits_index::<Idx, _>(text));

    let mut sa: Box<_> = (0..text.len()).map(Idx::from_usize).collect();
    sa.sort_by_key(|i| text.suffix(i.to_usize()));

    SuffixArray(sa)
}

pub fn sais(text: &[u8]) -> SuffixArray {
    let sa = sais::sais(text);
    // sa.verify(text);
    sa
}

// TODO move this to TextExt?
pub fn fits_index<Idx: ArrayIndex, T>(text: &[T]) -> bool {
    text.len() <= Idx::MAX.to_usize()
}

pub const fn one<Idx: ArrayIndex>() -> Idx { Idx::ONE }

pub const fn zero<Idx: ArrayIndex>() -> Idx { Idx::ZERO }

pub trait ToIndex<Idx: ArrayIndex> {
    fn to_index(self) -> Idx;
}

impl<Idx: ArrayIndex> ToIndex<Idx> for usize {
    fn to_index(self) -> Idx { Idx::from_usize(self) }
}

// TODO move this somewhere it makes more sense
#[rustfmt::skip]
pub trait ArrayIndex: 'static + Sized + Copy + Ord + Debug
    + Add<Output = Self> + AddAssign + Sub<Output = Self> + SubAssign
{
    const MAX: Self;
    const ZERO: Self;
    const ONE: Self;

    fn to_usize(self) -> usize;

    fn from_usize(value: usize) -> Self;
}

impl ArrayIndex for usize {
    const MAX: Self = usize::MAX;
    const ONE: Self = 1;
    const ZERO: Self = 0;

    fn to_usize(self) -> usize { self }

    fn from_usize(value: usize) -> Self { value }
}

impl ArrayIndex for u8 {
    const MAX: Self = u8::MAX;
    const ONE: Self = 1;
    const ZERO: Self = 0;

    fn to_usize(self) -> usize { self.into() }

    fn from_usize(value: usize) -> Self { value as u8 }
}

impl ArrayIndex for u16 {
    const MAX: Self = u16::MAX;
    const ONE: Self = 1;
    const ZERO: Self = 0;

    fn to_usize(self) -> usize { self.into() }

    fn from_usize(value: usize) -> Self { value as u16 }
}

#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
impl ArrayIndex for u32 {
    const MAX: Self = u32::MAX;
    const ONE: Self = 1;
    const ZERO: Self = 0;

    fn to_usize(self) -> usize { self as usize }

    fn from_usize(value: usize) -> Self { value as u32 }
}

#[cfg(target_pointer_width = "64")]
impl ArrayIndex for u64 {
    const MAX: Self = u64::MAX;
    const ONE: Self = 1;
    const ZERO: Self = 0;

    fn to_usize(self) -> usize { self as usize }

    fn from_usize(value: usize) -> Self { value as u64 }
}
