use std::iter::zip;
use std::marker::PhantomData;
use std::mem;
use std::slice;

use self::kind::BucketExt;
use self::kind::{Begin, BucketKind, End};
use crate::num::one;
use crate::num::zero;
use crate::num::{ArrayIndex, AsPrimitive};
use crate::sa::alphabet::Alphabet;
use crate::text::Text;

fn buckets<Idx: ArrayIndex>(alphabet: impl Alphabet) -> Box<[Idx]> {
    vec![zero(); alphabet.size()].into_boxed_slice()
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

// TODO add the histogram to the buckets
#[derive(Debug, Clone)]
pub(super) struct Buckets<A, Idx, K> {
    pub inner: Box<[Idx]>,
    _phantom: PhantomData<(A, K)>,
}

impl<A: Alphabet, Idx: ArrayIndex, K: BucketKind> Buckets<A, Idx, K> {
    pub fn new(alphabet: A) -> Self {
        Self { inner: buckets(alphabet), _phantom: PhantomData }
    }

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
    use core::slice::IterMut;
    use std::{
        iter::{zip, Zip},
        ops::Add,
    };

    use super::Buckets;
    use crate::{
        num::{zero, ArrayIndex},
        sa::alphabet::Alphabet,
    };

    #[derive(Debug, Clone, Copy)]
    pub struct Begin;

    #[derive(Debug, Clone, Copy)]
    pub struct End;

    pub trait BucketKind {
        fn next<T: Add<Output = T>>(sum: T, n: T) -> T;
    }

    impl BucketKind for Begin {
        fn next<T: Add<Output = T>>(sum: T, _: T) -> T { sum }
    }

    impl BucketKind for End {
        fn next<T: Add<Output = T>>(sum: T, n: T) -> T { sum + n }
    }

    pub trait BucketExt<Idx> {
        fn write(&mut self, histogram: &[Idx]);
    }

    impl<A: Alphabet, Idx: ArrayIndex, K0: BucketKind, K1: BucketKind> BucketExt<Idx>
        for (&mut Buckets<A, Idx, K0>, &mut Buckets<A, Idx, K1>)
    {
        fn write(&mut self, histogram: &[Idx]) {
            let iter = zip(&mut *self.0.inner, &mut *self.1.inner);
            iter.zip(histogram).fold(zero(), |sum, ((begin, end), &n)| {
                *begin = K0::next(sum, n);
                *end = K1::next(sum, n);
                sum + n
            });
        }
    }

    #[rustfmt::skip]
    impl< A: Alphabet, Idx: ArrayIndex, K0: BucketKind, K1: BucketKind, K2: BucketKind> BucketExt<Idx>
        for (&mut Buckets<A, Idx, K0>, &mut Buckets<A, Idx, K1>, &mut Buckets<A, Idx, K2>)
    {
        fn write(&mut self, histogram: &[Idx]) {
            let iter = zip(&mut *self.0.inner, &mut *self.1.inner);
            let iter = zip(iter, &mut *self.2.inner);
            iter.zip(histogram).fold(zero(), |sum, (((k0, k1), k2), &n)| {
                *k0 = K0::next(sum, n);
                *k1 = K1::next(sum, n);
                *k2 = K2::next(sum, n);
                sum + n
            });
        }
    }
}
