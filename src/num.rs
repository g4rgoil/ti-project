//! A number of traits to allow for generic numeric types and arithmetic.
//!
//! This module is strongly inspired by the [`num_traits`](https://docs.rs/num-traits/latest/num_traits/) crate and strongly
//! mirrors its structure.

use std::{fmt, ops};

/// Returns the `1` element for `T`.
pub const fn one<T: One>() -> T { T::ONE }

/// Returns the `0` element for `T`.
pub const fn zero<T: Zero>() -> T { T::ZERO }

/// Base trait for primitve integers.
///
/// Covers basic constants, numeric operations, and logical operations. Types
/// are expected to behave like fixed-size integers (e.g. `u8`, `i32`, ...).
pub trait PrimInt:
    Sized
    + Default
    + Copy
    + Ord
    + Num
    + Limits
    + ops::Not<Output = Self>
    + ops::BitAnd<Output = Self>
    + ops::BitAndAssign
    + ops::BitOr<Output = Self>
    + ops::BitOrAssign
    + ops::BitXor<Output = Self>
    + ops::BitXorAssign
    + fmt::Debug
{
    const BITS: u32;
}

/// Base trait for numeric types with `0` and `1` values, as well as basic
/// numeric operations and equality operation.
pub trait Num: PartialEq + Zero + One + NumOps {}

/// Defines the additive identity element for `Self`.
pub trait Zero {
    const ZERO: Self;
}

/// Defines the multiplicative identity element for `Self`.
pub trait One {
    const ONE: Self;
}

/// Defines the upper and lower limit for `Self`.
pub trait Limits {
    const MIN: Self;
    const MAX: Self;
}

/// A trait for types implementing basic numeric operations.
pub trait NumOps:
    Sized
    + ops::Add<Output = Self>
    + ops::AddAssign
    + ops::Sub<Output = Self>
    + ops::SubAssign
    + ops::Mul<Output = Self>
    + ops::MulAssign
    + ops::Div<Output = Self>
    + ops::DivAssign
{
}

#[doc(hidden)]
macro_rules! impl_prim_int {
    ($( $type:ty ),*) => {
        $(
            impl PrimInt for $type { const BITS: u32 = <$type>::BITS; }
            impl Num for $type { }
            impl Zero for $type { const ZERO: Self = 0; }
            impl One for $type { const ONE: Self = 1; }
            impl Limits for $type {
                const MIN: Self = Self::MIN;
                const MAX: Self = Self::MAX;
            }
            impl NumOps for $type {}
        )*
    };
}

impl_prim_int!(u8, i8, u16, i16, u32, i32, u64, i64, usize, isize);

/// A trait for types with signed and unsigned versions.
pub trait IntTypes {
    type Signed: IntTypes + Signed;
    type Unsigned: IntTypes + Unsigned;
}

/// Defines operations for signed types.
pub trait Signed: Num + ops::Neg<Output = Self> {
    fn is_positive(&self) -> bool;
    fn is_negative(&self) -> bool;
}

#[doc(hidden)]
macro_rules! impl_signed {
    ($( $type:ty ),*) => {
        $( impl Signed for $type {
            #[inline(always)]
            fn is_positive(&self) -> bool { <$type>::is_positive(*self) }

            #[inline(always)]
            fn is_negative(&self) -> bool { <$type>::is_negative(*self) }
        } )*
    };
}

impl_signed!(i8, i16, i32, i64, isize);

/// A trait for values wich cannot be negative.
pub trait Unsigned: Num {}

#[doc(hidden)]
macro_rules! impl_unsigned {
    ($( $type:ty ),*) => {
        $( impl Unsigned for $type { } )*
    };
}

impl_unsigned!(u8, u16, u32, u64, usize);

#[doc(hidden)]
macro_rules! impl_int_types {
    ($( $unsigned:ty => $signed:ty ),*) => {
        $( impl IntTypes for $unsigned {
            type Signed = $signed;
            type Unsigned = $unsigned;
        })*
        $( impl IntTypes for $signed {
            type Signed = $signed;
            type Unsigned = $unsigned;
        })*
    };
}

impl_int_types!(u8 => i8, u16 => i16, u32 => i32, u64 => i64, usize => isize);

/// A trait counterpart to the builtin primitve casts.
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
