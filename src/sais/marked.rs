use std::fmt;

use crate::prelude::*;

/// A wrapper around signed integers which uses the sign bit to distinguish
/// between _marked_ and _unmarked_ values.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
#[repr(transparent)]
pub struct Markable<T>(T);

impl<T: One> One for Markable<T> {
    const ONE: Self = Self(T::ONE);
}

impl<T: Zero> Zero for Markable<T> {
    const ZERO: Self = Self(T::ZERO);
}

#[allow(unused)]
impl<T: ArrayIndex + Signed> Markable<T> {
    /// Return an unmarked `Markable` with the given `value`.
    pub fn new(value: T) -> Self {
        debug_assert!(!value.is_negative());
        Self(value)
    }

    /// Return `true` iff `self` is marked.
    pub fn is_marked(&self) -> bool { self.0.is_negative() }

    /// Return `true` iff `self` is unmarked.
    pub fn is_unmarked(&self) -> bool { !self.0.is_negative() }

    /// Return `true` iff `self` is marked and its value is positive.
    pub fn is_marked_positive(&self) -> bool { self.inverse().0.is_positive() }

    /// Return `true` iff `self` is unmarked and its value is positive.
    pub fn is_unmarked_positive(&self) -> bool { self.0.is_positive() }

    /// Return the `value` of `self`.
    pub fn get(&self) -> T { self.0 & T::MAX }

    /// Return a marked `Markable` with the same value as `self`.
    pub fn marked(&self) -> Self { Self(self.0 | T::MIN) }

    /// Return an unmarked `Markable` with the same value as `self`.
    pub fn unmarked(&self) -> Self { Self(self.get()) }

    /// Return a `Markable` which is marked iff `self` is unmarked.
    pub fn inverse(&self) -> Self { Self(self.0 ^ T::MIN) }

    /// Return a `Markable` which is marked iff `pred` is `true`.
    pub fn marked_if(&self, pred: bool) -> Self {
        Self(self.0 | ((pred as usize) << (T::BITS - 1)).to_index())
    }
}

impl<T> Markable<T> {
    /// Safely cast a slice of `T`s to a slice of `Markable<T>`.
    pub fn cast_mut_slice(slice: &mut [T]) -> &mut [Self] {
        // Safety: `Markable<T>` has the same layout as `T`.
        unsafe { &mut *(slice as *mut _ as *mut _) }
    }
}

impl<T: ArrayIndex + Signed> fmt::Debug for Markable<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_marked() {
            write!(f, "!{:?}", self.0)
        } else {
            write!(f, "{:?}", self.0)
        }
    }
}
