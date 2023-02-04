// TODO
//! Most of the functionality in this module could be replaced with appropriate
//! imports from the num_traits crate.

use std::fmt::Debug;
use std::ops::{Add, AddAssign, Neg, Sub, SubAssign};

pub const fn one<T: One>() -> T { T::ONE }

pub const fn zero<T: Zero>() -> T { T::ZERO }


// TODO free functions like one, zero
// TODO maybe impls for ref types???
// TODO rename mod to num
// TODO rename this to something meaningful like PrimInt?!
// TODO where std::ops::Range: DoubleEndedIterator to emulate Step?!
/// A trait for types that can be used to index texts.
pub trait ArrayIndex:
    Sized
    + Copy
    + Ord
    + Debug
    + Zero
    + One
    + Limits
    + AsPrimitive<usize>
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
{
    fn from_usize(value: usize) -> Self;
}

#[doc(hidden)]
macro_rules! impl_array_index {
    ($( $type:ty ),*) => {
        $( impl ArrayIndex for $type {
            #[inline(always)]
            fn from_usize(value: usize) -> Self { value as Self }
        } )*
    };
}

impl_array_index!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize);

// TODO are these needed
// #[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
// #[cfg(target_pointer_width = "64")]

/// An extensions trait to convert `usize`s to [`ArrayIndex`]s.
pub trait ToIndex<Idx: ArrayIndex> {
    /// Convert `self` to a value of type `Idx` using a primitive cast.
    fn to_index(self) -> Idx;
}

impl<Idx: ArrayIndex> ToIndex<Idx> for usize {
    #[inline(always)]
    fn to_index(self) -> Idx { Idx::from_usize(self) }
}

/// A trait for conversions between primitive integers. Pretty much a straight
/// copy of the equally named trait in the `num_traits` crate.
pub trait AsPrimitive<T>: 'static + Copy {
    /// Coverts `self` to a value of type `T` using a primitve cast. This
    /// functions is explicitly allowed to lose information.
    fn as_(self) -> T;
}

#[doc(hidden)]
macro_rules! impl_as_primitive {
    ($($src:ty),+ => $dst:ty ) => {
        $(
            impl AsPrimitive<$dst> for $src {
                #[inline(always)]
                fn as_(self) -> $dst { self as $dst }
            }
        )+
    };
}

impl_as_primitive!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize => u8);
impl_as_primitive!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize => i8);
impl_as_primitive!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize => u16);
impl_as_primitive!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize => i16);
impl_as_primitive!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize => u32);
impl_as_primitive!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize => i32);
impl_as_primitive!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize => u64);
impl_as_primitive!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize => i64);
impl_as_primitive!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize => usize);
impl_as_primitive!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize => isize);


pub trait Zero {
    const ZERO: Self;
}

pub trait One {
    const ONE: Self;
}

pub trait Limits {
    const MIN: Self;
    const MAX: Self;
}

#[doc(hidden)]
macro_rules! impl_constants {
    ($( $type:ty ),*) => {
        $(
            impl Zero for $type { const ZERO: Self = 0; }
            impl One for $type { const ONE: Self = 1; }
            impl Limits for $type {
                const MIN: Self = Self::MIN;
                const MAX: Self = Self::MAX;
            }
        )*
    };
}

impl_constants!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize);

pub trait Signed: Sized + Neg<Output = Self> {
    fn abs(&self) -> Self;
    fn is_positive(&self) -> bool;
    fn is_negative(&self) -> bool;
}

#[doc(hidden)]
macro_rules! impl_signed {
    ($( $type:ty ),*) => {
        $( impl Signed for $type {
            #[inline(always)]
            fn abs(&self) -> Self { <$type>::abs(*self) }

            #[inline(always)]
            fn is_positive(&self) -> bool { <$type>::is_positive(*self) }

            #[inline(always)]
            fn is_negative(&self) -> bool { <$type>::is_negative(*self) }
        } )*
    };
}

impl_signed!(i8, i16, i32, i64, isize);

// TODO better name for this
// TODO add transmutable bounds to this?
pub trait IntegerTypes {
    type Signed: IntegerTypes;
    type Unsigned: IntegerTypes;
}

#[doc(hidden)]
macro_rules! impl_int_types {
    ($( $unsigned:ty => $signed:ty ),*) => {
        $( impl IntegerTypes for $unsigned {
            type Signed = $signed;
            type Unsigned = $unsigned;
        })*
        $( impl IntegerTypes for $signed {
            type Signed = $signed;
            type Unsigned = $unsigned;
        })*
    };
}

impl_int_types!(u8 => i8, u16 => i16, u32 => i32, u64 => i64, usize => isize);
