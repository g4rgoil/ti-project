mod sais;

use std::fmt::Debug;
use std::iter::zip;

use self::result::MemoryResult;
use crate::index::{ArrayIndex, ToIndex};
use crate::text::Text;

#[allow(unused)]
pub fn naive<T: Ord + Debug, Idx: ArrayIndex>(text: &Text<T>) -> SuffixArray<T, Idx> {
    assert!(text.fits_index::<Idx>());

    let mut sa: Box<_> = (0..text.len()).map(Idx::from_usize).collect();
    sa.sort_by_key(|i| &text[*i..]);

    SuffixArray { text, sa }
}

pub fn sais<Idx: ArrayIndex>(text: &Text<u8>) -> MemoryResult<SuffixArray<u8, Idx>> {
    sais::sais(text)
}

/// TODO: Invariants:
/// - sa is permutation of (0, sa.len())
/// TODO add reference to text
/// TODO remove Array Index bound
#[derive(Debug, Clone)]
pub struct SuffixArray<'txt, T, Idx> {
    text: &'txt Text<T>,
    sa: Box<[Idx]>,
}

impl<'txt, T, Idx: ArrayIndex> SuffixArray<'txt, T, Idx> {
    pub fn text(&self) -> &'txt Text<T> { self.text }

    pub fn inner(&self) -> &[Idx] { &self.sa }

    #[inline(never)]
    pub fn inverse(&self) -> InverseSuffixArray<'txt, '_, T, Idx> {
        // TODO use MaybeUninit for optimization

        let mut isa = vec![Idx::ZERO; self.sa.len()];

        for (i, sa_i) in self.sa.iter().enumerate() {
            // SAFETY: Because a SuffixArray is a permutation of (0, len),
            // sa_i is guaranteed to not be out of bounds for isa
            unsafe { *isa.get_unchecked_mut(sa_i.as_()) = i.to_index() };
        }

        InverseSuffixArray { sa: self, isa: isa.into_boxed_slice() }
    }

    #[allow(unused)]
    pub fn verify(&self, text: &Text<T>)
    where
        T: Ord + Debug,
    {
        let is_increasing = zip(self.sa.iter(), self.sa.iter().skip(1))
            .all(|(i, j)| text[*i..] < text[*j..]);
        assert!(is_increasing, "the suffix array is not sorted in increasing order");


        let mut arr = vec![false; text.len()];
        self.sa.iter().for_each(|i| arr[i.as_()] = true);
        assert!(
            arr.iter().all(|b| *b),
            "the suffix array is not a permutation of [0..len)"
        );
    }
}

/// TODO: Invariants:
/// - sa is permutation of (0, sa.len())
#[derive(Debug, Clone)]
pub struct InverseSuffixArray<'sa, 'txt, T, Idx> {
    sa: &'sa SuffixArray<'txt, T, Idx>,
    isa: Box<[Idx]>,
}

impl<'sa, 'txt, T, Idx: ArrayIndex> InverseSuffixArray<'sa, 'txt, T, Idx> {
    pub fn sa(&self) -> &'sa SuffixArray<'txt, T, Idx> { self.sa }

    pub fn inner(&self) -> &[Idx] { &self.isa }
}

pub mod result {
    use std::marker::PhantomData;

    #[derive(Debug, Clone, Copy)]
    #[must_use]
    pub struct MemoryResult<T> {
        pub value: T,
        pub memory: usize,
    }

    impl<T> MemoryResult<T> {
        pub fn builder() -> Builder<T> {
            Builder { memory: 0, _phantom: Default::default() }
        }

        pub fn add_to<S>(self, builder: &mut Builder<S>) -> T {
            builder.memory += self.memory;
            self.value
        }
    }

    #[derive(Debug, Clone, Copy)]
    pub struct Builder<T> {
        pub memory: usize,
        _phantom: PhantomData<T>,
    }

    impl<T> Builder<T> {
        pub fn build(self, value: T) -> MemoryResult<T> {
            MemoryResult { value, memory: self.memory }
        }

        pub fn add_values<S>(&mut self, num: usize) {
            self.memory += num * std::mem::size_of::<S>();
        }
    }
}
