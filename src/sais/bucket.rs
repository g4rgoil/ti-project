use std::marker::PhantomData;
use std::mem;
use std::slice;

use self::kind::{Begin, BucketKind, End, Invalid};
use super::alphabet::Alphabet;
use crate::num::one;
use crate::num::{ArrayIndex, AsPrimitive};
use crate::text::Text;

fn buckets<Idx: ArrayIndex>(alphabet: impl Alphabet) -> Box<[Idx]> {
    vec![Idx::ZERO; alphabet.size()].into_boxed_slice()
}

pub(super) fn histogram<A: Alphabet, Idx: ArrayIndex>(
    text: &Text<A::Symbol>,
    alphabet: A,
) -> Box<[Idx]> {
    let mut histogram = buckets::<Idx>(alphabet);
    for c in text {
        histogram[c.as_()] += one();
    }
    histogram
}

// TODO Buckets still needs a major rework
// TODO add the histogram to the buckets
#[derive(Debug, Clone)]
pub(super) struct Buckets<A: Alphabet, Idx: ArrayIndex, K> {
    pub inner: Box<[Idx]>,
    _phantom: PhantomData<(A, K)>,
}

impl<A: Alphabet, Idx: ArrayIndex> Buckets<A, Idx, Invalid> {
    pub fn new(alphabet: A) -> Self {
        Self { inner: buckets(alphabet), _phantom: PhantomData }
    }
}

impl<A: Alphabet, Idx: ArrayIndex, K> Buckets<A, Idx, K> {
    // TODO take &mut self instead somehow
    #[must_use]
    pub fn write<L: BucketKind>(mut self, histogram: &[Idx]) -> Buckets<A, Idx, L> {
        let iter = self.inner.iter_mut().zip(histogram);
        iter.fold(Idx::ZERO, |sum, (dst, n)| {
            *dst = L::next(sum, *n);
            sum + *n
        });

        Buckets { inner: self.inner, _phantom: PhantomData }
    }

    pub fn invalidate(mut self) -> Buckets<A, Idx, Invalid> {
        Buckets { inner: self.inner, _phantom: PhantomData }
    }
}

impl<A: Alphabet, Idx: ArrayIndex, K: BucketKind> Buckets<A, Idx, K> {
    pub fn get(&self, symbol: A::Symbol) -> Idx { self.inner[symbol.as_()] }

    pub fn iter(&self) -> slice::Iter<Idx> { self.inner.iter() }
}

impl<A: Alphabet, Idx: ArrayIndex> Buckets<A, Idx, Begin> {
    pub fn take_first(&mut self, symbol: A::Symbol) -> Idx {
        let idx = &mut self.inner[symbol.as_()];
        mem::replace(idx, *idx + one())
    }
}

impl<A: Alphabet, Idx: ArrayIndex> Buckets<A, Idx, End> {
    pub fn take_last(&mut self, symbol: A::Symbol) -> Idx {
        let idx = &mut self.inner[symbol.as_()];
        *idx -= one();
        *idx
    }
}

// TODO ???????
pub(super) mod kind {
    use std::ops::Add;

    #[derive(Debug, Clone, Copy)]
    pub struct Begin;

    #[derive(Debug, Clone, Copy)]
    pub struct End;

    #[derive(Debug, Clone, Copy)]
    pub struct Invalid;

    pub trait BucketKind {
        fn next<T: Add<Output = T>>(sum: T, n: T) -> T;
    }

    impl BucketKind for Begin {
        fn next<T: Add<Output = T>>(sum: T, _: T) -> T { sum }
    }

    impl BucketKind for End {
        fn next<T: Add<Output = T>>(sum: T, n: T) -> T { sum + n }
    }
}
