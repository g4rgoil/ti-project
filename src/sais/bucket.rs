use std::iter::zip;
use std::marker::PhantomData;
use std::ops;

use crate::prelude::*;
use crate::sa::alphabet::Symbol;


pub(super) struct Buckets<'a, Idx, K> {
    inner: &'a mut [Idx],
    _phantom: PhantomData<K>,
}

impl<'a, Idx: ArrayIndex, K: BucketKind> Buckets<'a, Idx, K> {
    pub fn write(slice: &'a mut [Idx], histogram: &[Idx]) -> Self {
        let mut sum = zero();
        for (k, n) in zip(&mut *slice, histogram) {
            *k = K::next(sum, *n);
            sum += *n;
        }
        Self { inner: slice, _phantom: PhantomData }
    }

    pub fn iter(&self) -> std::slice::Iter<Idx> { self.inner.iter() }
}

impl<'a, Idx: ArrayIndex> Buckets<'a, Idx, Begin> {
    pub fn take_first(&mut self, symbol: impl Symbol) -> Idx {
        let idx = &mut self.inner[symbol.as_()];
        std::mem::replace(idx, *idx + one())
    }
}

impl<'a, Idx: ArrayIndex> Buckets<'a, Idx, End> {
    pub fn take_last(&mut self, symbol: impl Symbol) -> Idx {
        let idx = &mut self.inner[symbol.as_()];
        *idx -= one();
        *idx
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Begin;

#[derive(Debug, Clone, Copy)]
pub struct End;

pub trait BucketKind {
    fn next<T: ops::Add<Output = T>>(sum: T, n: T) -> T;
}

impl BucketKind for Begin {
    fn next<T: ops::Add<Output = T>>(sum: T, _: T) -> T { sum }
}

impl BucketKind for End {
    fn next<T: ops::Add<Output = T>>(sum: T, n: T) -> T { sum + n }
}
