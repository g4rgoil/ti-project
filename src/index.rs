use std::fmt::Debug;
use std::ops::{Add, AddAssign, Sub, SubAssign};

// TODO where std::ops::Range: DoubleEndedIterator to emulate Step?!
pub trait ArrayIndex:
    Sized
    + Copy
    + Ord
    + Debug
    + AsPrimitive<usize>
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
{
    const MAX: Self;
    const ZERO: Self;
    const ONE: Self;

    fn from_usize(value: usize) -> Self;
}

impl ArrayIndex for usize {
    const MAX: Self = usize::MAX;
    const ONE: Self = 1;
    const ZERO: Self = 0;

    fn from_usize(value: usize) -> Self { value }
}

impl ArrayIndex for u8 {
    const MAX: Self = u8::MAX;
    const ONE: Self = 1;
    const ZERO: Self = 0;

    fn from_usize(value: usize) -> Self { value as u8 }
}

impl ArrayIndex for u16 {
    const MAX: Self = u16::MAX;
    const ONE: Self = 1;
    const ZERO: Self = 0;

    fn from_usize(value: usize) -> Self { value as u16 }
}

#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
impl ArrayIndex for u32 {
    const MAX: Self = u32::MAX;
    const ONE: Self = 1;
    const ZERO: Self = 0;

    fn from_usize(value: usize) -> Self { value as u32 }
}

#[cfg(target_pointer_width = "64")]
impl ArrayIndex for u64 {
    const MAX: Self = u64::MAX;
    const ONE: Self = 1;
    const ZERO: Self = 0;

    fn from_usize(value: usize) -> Self { value as u64 }
}

pub trait ToIndex<Idx: ArrayIndex> {
    fn to_index(self) -> Idx;
}

impl<Idx: ArrayIndex> ToIndex<Idx> for usize {
    fn to_index(self) -> Idx { Idx::from_usize(self) }
}

pub trait AsPrimitive<T>: 'static + Copy {
    fn as_(self) -> T;
}

macro_rules! impl_as_primitive {
    ($($src:ty),+ => $dst:ty ) => {
        $(
            impl AsPrimitive<$dst> for $src {
                fn as_(self) -> $dst { self as $dst }
            }
        )+
    };
}

impl_as_primitive!(u8, u16, u32, u64, usize => usize);
