use std::iter::zip;
use std::marker::PhantomData;

use crate::prelude::*;
use crate::sa::alphabet::Symbol;


/// TODO doc
pub struct Buckets<'a, Idx, K> {
    pub inner: &'a mut [Idx],
    _phantom: PhantomData<K>,
}

impl<'a, Idx: ArrayIndex, K: Kind> Buckets<'a, Idx, K> {
    pub fn write(slice: &'a mut [Idx], histogram: &[Idx]) -> Self {
        let mut sum = zero();
        for (k, n) in zip(&mut *slice, histogram) {
            *k = K::next(sum, *n);
            sum += *n;
        }
        Self { inner: slice, _phantom: PhantomData }
    }

    pub fn take(&mut self, symbol: impl Symbol) -> Idx {
        K::take(&mut self.inner[symbol.as_()])
    }
}

pub struct Begin;

pub struct End;

pub trait Kind {
    fn next<T: Num>(sum: T, n: T) -> T;

    fn take<T: Num + Copy>(bucket: &mut T) -> T;
}

impl Kind for Begin {
    fn next<T: Num>(sum: T, _: T) -> T { sum }

    fn take<T: Num + Copy>(bucket: &mut T) -> T {
        std::mem::replace(bucket, *bucket + one())
    }
}

impl Kind for End {
    fn next<T: Num>(sum: T, n: T) -> T { sum + n }

    fn take<T: Num + Copy>(bucket: &mut T) -> T {
        *bucket -= one();
        *bucket
    }
}
