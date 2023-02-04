use std::iter::zip;
use std::marker::PhantomData;

use crate::prelude::*;
use crate::sa::alphabet::Symbol;


/// Represents the buckets used by the implementation of SAIS.
///
/// Internally this is simply a wrapper around a slice. The generic type `K`
/// represents the _kind_ (see also [`Kind`]) of the buckets, i.e. whether they
/// point to the beginning or end of a bucket (see also [`Begin`], [`End`]).
pub struct Buckets<'a, Idx, K> {
    pub inner: &'a mut [Idx],
    _phantom: PhantomData<K>,
}

impl<'a, Idx: ArrayIndex, K: Kind> Buckets<'a, Idx, K> {
    /// Write buckets to `slice` according to `hisogram` and the chosen [`Kind`].
    pub fn new(slice: &'a mut [Idx], histogram: &[Idx]) -> Self {
        let mut sum = zero();
        for (k, n) in zip(&mut *slice, histogram) {
            *k = K::next(sum, *n);
            sum += *n;
        }
        Self { inner: slice, _phantom: PhantomData }
    }

    /// Return the next index in the bucket for `symbol` and internally increase
    /// its size by 1. If used incorrectly, this methods may panic itself or
    /// lead to out of bound accesses elsewhere.
    pub fn take(&mut self, symbol: impl Symbol) -> Idx {
        K::take(&mut self.inner[symbol.as_()])
    }
}

/// A trait used to define the behaviour and implemenation of [`Buckets`].
pub trait Kind {
    /// Returns the index of the next bucket. Used by [`Buckets::new`] during
    /// initialization. The value `sum` gives the sume of all previous positions
    /// in the historam, while `n` gives the current value.
    fn next<T: Num>(sum: T, n: T) -> T;

    /// Returns the next index in `bucket` and internally increase its size by one.
    fn take<T: Num + Copy>(bucket: &mut T) -> T;
}

/// Indicates buckets that grow to the right (equivalent to a post-increment).
pub struct Begin;

impl Kind for Begin {
    fn next<T: Num>(sum: T, _: T) -> T { sum }

    fn take<T: Num + Copy>(bucket: &mut T) -> T {
        std::mem::replace(bucket, *bucket + one())
    }
}

/// Indicates buckets that grow to the left (equivalent to a pre-decrement).
pub struct End;

impl Kind for End {
    fn next<T: Num>(sum: T, n: T) -> T { sum + n }

    fn take<T: Num + Copy>(bucket: &mut T) -> T {
        *bucket -= one();
        *bucket
    }
}
