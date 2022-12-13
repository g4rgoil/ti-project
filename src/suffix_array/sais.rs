use std::iter::zip;

use self::alphabet::{Alphabet, ByteAlphabet, IndexAlphabet, IndexSymbol};
use self::buckets::Buckets;
use self::lms::LMSIter;
use super::SuffixArray;
use crate::index::{ArrayIndex, ToIndex};
use crate::sa::index;
use crate::sa::sais::lms::lms_str_from_suffix;
use crate::TextExt;

pub(super) fn sais(text: &[u8]) -> SuffixArray {
    SuffixArray(sais_impl::<_, usize>(text, ByteAlphabet))
}


fn sais_impl<A: Alphabet, Idx: ArrayIndex>(
    text: &[A::Symbol],
    alphabet: A,
) -> Box<[Idx]> {
    assert!(index::fits::<Idx, _>(text));

    // TODO fix this
    if text.is_empty() {
        return Box::new([]);
    }

    let mut sa = vec![Idx::ZERO; text.len()];
    let mut buckets = Buckets::new(text, alphabet);

    // TODO the handling of buckets is weird here
    let (mut lms_buckets, mut lms_sorted) =
        partial_sort_lms_strs(text, &mut sa, &mut buckets);

    // Write rank of LMS-substring into the suffix array
    let mut iter = lms_sorted
        .iter()
        .map(|i| (i, lms_str_from_suffix(text.suffix(i.to_usize()))))
        .peekable();

    let mut rank = Idx::ZERO;
    while let (Some((i, prev)), next) = (iter.next(), iter.peek()) {
        sa[i.to_usize()] = rank;
        if next.map_or(true, |(_, next)| &prev != next) {
            rank += Idx::ONE;
        }
    }

    if rank.to_usize() == lms_sorted.len() {
        let mut lms_iter = lms_sorted.iter();
        let lms_bucket_begin = lms_buckets.end.as_ref();
        let lms_bucket_end = &lms_buckets.begin.as_ref()[1..];

        sa.fill(Idx::ZERO);
        for (&i, &j) in zip(lms_bucket_begin, lms_bucket_end) {
            zip(&mut sa[i.to_usize()..j.to_usize()], lms_iter.by_ref())
                .for_each(|(dst, lms)| *dst = *lms);
        }
    } else {
        sort_lms_recursive(text, &mut sa, &mut lms_buckets, &mut lms_sorted);
    }

    // Reset LMS buckets to initial state
    let (last, head) = lms_buckets.end.as_mut().split_last_mut().unwrap();
    head.clone_from_slice(&lms_buckets.begin.as_ref()[1..]);
    *last = text.len().to_index();

    induce_l_suffixes(text, &mut sa, &mut lms_buckets);
    induce_s_suffixes(text, &mut sa, &mut lms_buckets);

    sa.into_boxed_slice()
}


// TODO need to  be specific here about post conditions
fn partial_sort_lms_strs<A: Alphabet, Idx: ArrayIndex>(
    text: &[A::Symbol],
    sa: &mut [Idx],
    buckets: &mut Buckets<A, Idx>,
) -> (Buckets<A, Idx>, Box<[Idx]>) {
    let mut lms_buckets = buckets.clone();

    let lms_count = LMSIter::new(text)
        .inspect(|&lms| {
            let idx = lms_buckets.get_mut(text[lms]).take_last();
            sa[idx.to_usize()] = lms.to_index();
        })
        .count();

    // Induce partial order among LMS-substrings
    induce_l_suffixes(text, sa, buckets);
    induce_s_suffixes(text, sa, buckets);

    // Collect LMS-prefixes, sorted by LMS-substrings
    // NOTE disgregarding the last bucket here
    let s_bucket_begin = buckets.end.as_ref();
    let s_bucket_end = &lms_buckets.begin.as_ref()[1..];

    let mut lms_sorted = Vec::with_capacity(lms_count);
    lms_sorted.extend(
        zip(s_bucket_begin, s_bucket_end)
            .flat_map(|(&i, &j)| &sa[i.to_usize()..j.to_usize()])
            .filter(|&&i| i > Idx::ZERO)
            .filter(|&&i| text[i.to_usize() - 1] > text[i.to_usize()])
            .copied(),
    );

    (lms_buckets, lms_sorted.into_boxed_slice())
}

fn sort_lms_recursive<A: Alphabet, Idx: ArrayIndex>(
    text: &[A::Symbol],
    sa: &mut [Idx],
    lms_buckets: &mut Buckets<A, Idx>,
    lms_sorted: &mut [Idx],
) {
    // TODO case distinction alphabet_size ?= text_size
    // TODO use u8, u16, u32, u64 depending on lms_count
    // TODO Move this to the alphabet trait
    let mut lms_text = vec![IndexSymbol(Idx::ZERO); lms_sorted.len()];
    let lms_alphabet = IndexAlphabet::new(lms_sorted.len());

    // TODO benchmark what is better here (don't forget sa.fill(MAX))
    // .zip(sa.iter().enumerate().rev().filter(|(_, x)| **x != usize::MAX))
    for ((dst_symbol, dst_index), i) in (lms_text.iter_mut().rev())
        .zip(lms_sorted.iter_mut().rev())
        .zip(LMSIter::new(text))
    {
        (*dst_symbol, *dst_index) = (IndexSymbol(sa[i]), i.to_index());
    }

    sa.fill(Idx::ZERO);
    let lms_sa = sais_impl::<_, Idx>(&lms_text, lms_alphabet);

    // Put the sorted LMS-suffixes at the end of the buckets
    let mut lms_iter = lms_sa.iter();
    let lms_bucket_begin = lms_buckets.end.as_ref();
    let lms_bucket_end = &lms_buckets.begin.as_ref()[1..];

    for (&i, &j) in zip(lms_bucket_begin, lms_bucket_end) {
        zip(&mut sa[i.to_usize()..j.to_usize()], lms_iter.by_ref())
            .for_each(|(dst, lms)| *dst = lms_sorted[lms.to_usize()]);
    }
}


fn induce_l_suffixes<A: Alphabet, Idx: ArrayIndex>(
    text: &[A::Symbol],
    sa: &mut [Idx],
    buckets: &mut Buckets<A, Idx>,
) {
    // Emulate S* suffix of guardian element
    if let Some(last) = text.last() {
        let idx = buckets.get_mut(*last).take_first();
        sa[idx.to_usize()] = (sa.len() - 1).to_index();
    }

    for i in 0..sa.len() {
        if sa[i] != Idx::ZERO {
            let text_lhs = text[sa[i].to_usize() - 1];
            let text_rhs = text[sa[i].to_usize()];
            let bucket = buckets.get(text_rhs);

            let ord = text_lhs.cmp(&text_rhs);
            if ord.is_gt() || (ord.is_eq() && i < bucket.begin().to_usize()) {
                let idx = buckets.get_mut(text_lhs).take_first();
                sa[idx.to_usize()] = sa[i] - Idx::ONE;
            }
        }
    }
}

fn induce_s_suffixes<A: Alphabet, Idx: ArrayIndex>(
    text: &[A::Symbol],
    sa: &mut [Idx],
    buckets: &mut Buckets<A, Idx>,
) {
    for i in (0..sa.len()).rev() {
        if sa[i] != Idx::ZERO {
            let text_lhs = text[sa[i].to_usize() - 1];
            let text_rhs = text[sa[i].to_usize()];
            let bucket = buckets.get(text_rhs);

            let ord = text_lhs.cmp(&text_rhs);
            if ord.is_lt() || (ord.is_eq() && i >= bucket.begin().to_usize()) {
                let idx = buckets.get_mut(text_lhs).take_last();
                sa[idx.to_usize()] = sa[i] - Idx::ONE;
            }
        }
    }
}


// TODO maybe move this up to suffix_array
pub(super) mod alphabet {
    use std::{fmt::Debug, marker::PhantomData};

    use crate::index::ArrayIndex;

    pub(super) trait Symbol: Sized + Copy + Ord + Debug {
        fn min_value() -> Self;
        fn to_index(self) -> usize;
    }

    // TODO what about i8, i16, ...

    impl Symbol for u8 {
        fn to_index(self) -> usize { self.into() }

        fn min_value() -> Self { 0 }
    }

    impl Symbol for u16 {
        fn to_index(self) -> usize { self.into() }

        fn min_value() -> Self { 0 }
    }

    impl Symbol for u32 {
        fn to_index(self) -> usize { self as usize }

        fn min_value() -> Self { 0 }
    }

    impl Symbol for u64 {
        fn to_index(self) -> usize { self as usize }

        fn min_value() -> Self { 0 }
    }

    impl Symbol for usize {
        fn to_index(self) -> usize { self }

        fn min_value() -> Self { 0 }
    }

    #[repr(transparent)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub(super) struct IndexSymbol<Idx: ArrayIndex>(pub Idx);

    impl<Idx: ArrayIndex> Symbol for IndexSymbol<Idx> {
        fn min_value() -> Self { Self(ArrayIndex::ZERO) }

        fn to_index(self) -> usize { Idx::to_usize(self.0) }
    }

    pub(super) trait Alphabet: Clone {
        type Buckets<T: Clone>: Clone + AsRef<[T]> + AsMut<[T]>;
        type Symbol: Symbol;

        fn size(&self) -> usize;

        fn buckets<T: ArrayIndex>(&self) -> Self::Buckets<T>;
    }

    #[derive(Debug, Clone, Copy)]
    pub(super) struct ByteAlphabet;

    impl Alphabet for ByteAlphabet {
        type Buckets<T: Clone> = [T; u8::MAX as usize + 1];
        type Symbol = u8;

        fn size(&self) -> usize { u8::MAX as usize + 1 }

        fn buckets<Idx: ArrayIndex>(&self) -> Self::Buckets<Idx> {
            [Idx::ZERO; u8::MAX as usize + 1]
        }
    }

    #[derive(Debug, Clone, Copy)]
    pub(super) struct IndexAlphabet<Idx> {
        size: usize,
        _phantom: PhantomData<Idx>,
    }

    impl<Idx: ArrayIndex> IndexAlphabet<Idx> {
        pub(super) fn new(size: usize) -> Self {
            Self { size, _phantom: Default::default() }
        }
    }

    impl<Idx: ArrayIndex> Alphabet for IndexAlphabet<Idx> {
        type Buckets<T: Clone> = Box<[T]>;
        type Symbol = IndexSymbol<Idx>;

        fn size(&self) -> usize { self.size }

        fn buckets<Idx2: ArrayIndex>(&self) -> Self::Buckets<Idx2> {
            vec![Idx2::ZERO; self.size].into_boxed_slice()
        }
    }
}

#[allow(dead_code)]
mod buckets {
    use std::{iter::zip, mem, ops::Deref};

    use super::alphabet::{Alphabet, Symbol};
    use crate::index::ArrayIndex;

    // TODO add separate type for LMSBuckets
    #[derive(Debug, Clone)]
    pub(super) struct Buckets<A: Alphabet, Idx: ArrayIndex> {
        alphabet: A,
        pub begin: A::Buckets<Idx>,
        pub end: A::Buckets<Idx>,
    }

    impl<A: Alphabet, Idx: ArrayIndex> Buckets<A, Idx> {
        pub fn new(text: &[A::Symbol], alphabet: A) -> Self {
            let mut histogram = alphabet.buckets::<Idx>();
            for c in text {
                histogram.as_mut()[c.to_index()] += Idx::ONE;
            }

            let mut buckets_begin = alphabet.buckets::<Idx>();
            let sum = &mut Idx::ZERO.clone();
            for (begin, n) in zip(buckets_begin.as_mut(), histogram.as_ref()) {
                *begin = mem::replace(sum, *sum + *n);
            }

            // Reuse histogram for bucket ends
            let mut buckets_end = histogram;
            let mut sum = Idx::ZERO;
            for end in buckets_end.as_mut() {
                sum += *end;
                *end = sum;
            }

            Buckets { begin: buckets_begin, end: buckets_end, alphabet }
        }

        pub fn get(&self, symbol: A::Symbol) -> Bucket<&Idx> {
            Bucket {
                begin: &self.begin.as_ref()[symbol.to_index()],
                end: &self.end.as_ref()[symbol.to_index()],
            }
        }

        pub fn get_mut(&mut self, symbol: A::Symbol) -> Bucket<&mut Idx> {
            Bucket {
                begin: &mut self.begin.as_mut()[symbol.to_index()],
                end: &mut self.end.as_mut()[symbol.to_index()],
            }
        }
    }

    #[derive(Debug, Clone)]
    pub(super) struct Bucket<T> {
        begin: T,
        end: T,
    }

    impl<Idx: ArrayIndex, T: Deref<Target = Idx>> Bucket<T> {
        pub fn begin(&self) -> Idx { *self.begin }

        pub fn end(&self) -> Idx { *self.end }
    }

    impl<Idx: ArrayIndex> Bucket<&mut Idx> {
        pub fn take_first(&mut self) -> Idx {
            mem::replace(self.begin, *self.begin + Idx::ONE)
        }

        pub fn take_last(&mut self) -> Idx {
            *self.end -= Idx::ONE;
            *self.end
        }
    }
}

mod lms {
    use core::slice;
    use std::iter::{Enumerate, Peekable, Rev};

    use super::alphabet::Symbol;

    // TODO maybe remove this entirely
    pub(super) struct LMSIter<'a, S> {
        text: Peekable<Rev<Enumerate<slice::Iter<'a, S>>>>,
        decreasing: bool,
    }

    impl<'a, S> LMSIter<'a, S> {
        pub(super) fn new(text: &'a [S]) -> Self {
            LMSIter {
                text: text.iter().enumerate().rev().peekable(),
                decreasing: false,
            }
        }
    }

    impl<'a, S: Symbol> Iterator for LMSIter<'a, S> {
        type Item = usize;

        fn next(&mut self) -> Option<Self::Item> {
            let mut curr = self.text.next()?;

            while let Some(&next) = self.text.peek() {
                if self.decreasing {
                    if next.1 > curr.1 {
                        self.decreasing = false;
                        return Some(curr.0);
                    }
                } else {
                    self.decreasing = next.1 < curr.1;
                }
                self.text.next();
                curr = next;
            }
            None
        }
    }

    pub(super) fn lms_str_from_suffix<S: Symbol>(suffix: &[S]) -> &[S] {
        // TODO is this the most efficient way possible?
        let (mut prev, mut increasing, mut end) = (S::min_value(), true, 0);
        for (i, &next) in suffix.iter().enumerate() {
            if increasing {
                (prev, increasing, end) = (next, prev <= next, i);
            } else if prev > next {
                (prev, end) = (next, i);
            } else if prev < next {
                break;
            }
        }
        &suffix[..=end]
    }
}


#[cfg(test)]
mod test {
    use super::{alphabet::ByteAlphabet, *};
    use crate::suffix_array as sa;

    const LOREM_IPSUM_LONG: &[u8] = b"Lorem ipsum dolor sit amet, officia \
        excepteur ex fugiat reprehenderit enim labore culpa sint ad nisi Lorem \
        pariatur mollit ex esse exercitation amet. Nisi anim cupidatat \
        excepteur officia. Reprehenderit nostrud nostrud ipsum Lorem est \
        aliquip amet voluptate voluptate dolor minim nulla est proident. \
        Nostrud officia pariatur ut officia. Sit irure elit esse ea nulla sunt \
        ex occaecat reprehenderit commodo officia dolor Lorem duis laboris \
        cupidatat officia voluptate. Culpa proident adipisicing id nulla nisi \
        laboris ex in Lorem sunt duis officia eiusmod. Aliqua reprehenderit \
        commodo ex non excepteur duis sunt velit enim. Voluptate laboris sint \
        cupidatat ullamco ut ea consectetur et est culpa et culpa duis.";

    const A: ByteAlphabet = ByteAlphabet;

    fn convert<I: ArrayIndex, J: ArrayIndex>(arr: &[I]) -> Box<[J]> {
        arr.iter().map(|i| i.to_usize().to_index()).collect()
    }

    macro_rules! assert_sais_eq {
        (($text:expr, $alphabet:expr), $sa:expr, $($type:ty),+ $(,)?) => {
            $(
                assert_eq!(
                    *$crate::suffix_array::sais::sais_impl::<_, $type>($text, $alphabet),
                    *$crate::suffix_array::sais::test::convert($sa)
                );
            )+
        };
    }

    #[test]
    #[ignore]
    fn test_lms_iter_empty() {
        let mut iter = lms::LMSIter::<u8>::new(&[]);
        assert_eq!(iter.next(), None);
    }

    #[test]
    #[ignore]
    fn test_lms_iter_slides() {
        let iter = lms::LMSIter::new(b"ababcabcabba\0");
        let result: Vec<usize> = iter.collect();
        assert_eq!(result, &[12, 8, 5, 2]);
    }

    #[test]
    fn test_lms_str_slides() {
        assert_eq!(lms::lms_str_from_suffix(b"abcabcabba"), b"abca");
        assert_eq!(lms::lms_str_from_suffix(b"abcabba"), b"abca");
        assert_eq!(lms::lms_str_from_suffix(b"abba"), b"abba");
    }

    #[test]
    fn test_lms_str_wikipedia() {
        assert_eq!(lms::lms_str_from_suffix(b"issiissippi"), b"issi");
        assert_eq!(lms::lms_str_from_suffix(b"iissippi"), b"iissi");
        assert_eq!(lms::lms_str_from_suffix(b"ippi"), b"ippi");
    }

    #[test]
    fn test_lms_str_dna() {
        assert_eq!(lms::lms_str_from_suffix(b"AACAACAAAT"), b"AACA");
        assert_eq!(lms::lms_str_from_suffix(b"AACAAAT"), b"AACA");
        assert_eq!(lms::lms_str_from_suffix(b"AAAT"), b"AAAT");
    }

    #[test]
    fn test_lms_str_bug() {
        assert_eq!(lms::lms_str_from_suffix(b"decbaedecaf"), b"decba");
        assert_eq!(lms::lms_str_from_suffix(b"aedecaf"), b"aed");
        assert_eq!(lms::lms_str_from_suffix(b"decaf"), b"deca");
        assert_eq!(lms::lms_str_from_suffix(b"af"), b"af");
    }

    #[test]
    fn test_lms_str_dna_bug() {
        assert_eq!(lms::lms_str_from_suffix(b"GTGGGACTGTGGAG"), b"GTGGGA");
        assert_eq!(lms::lms_str_from_suffix(b"ACTGTGGAG"), b"ACTG");
        assert_eq!(lms::lms_str_from_suffix(b"GTGGAG"), b"GTGGA");
        assert_eq!(lms::lms_str_from_suffix(b"AG"), b"AG");
    }

    #[test]
    fn test_sais_wikipedia_with_sentinel() {
        let text = b"immissiissippi\0";
        let sa = [14, 13, 6, 0, 10, 3, 7, 2, 1, 12, 11, 5, 9, 4, 8];
        assert_eq!(*sais_impl::<_, usize>(text, A), sa);
        assert_sais_eq!((text, A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_wikipedia_no_sentinel() {
        let text = b"immissiissippi";
        let sa = [13, 6, 0, 10, 3, 7, 2, 1, 12, 11, 5, 9, 4, 8];
        assert_eq!(*sais_impl::<_, usize>(text, A), sa);
        assert_sais_eq!((text, A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_slides_with_sentinel() {
        let text = b"ababcabcabba\0";
        let sa = [12, 11, 0, 8, 5, 2, 10, 1, 9, 6, 3, 7, 4];
        assert_eq!(*sais_impl::<_, usize>(text, A), sa);
        assert_sais_eq!((text, A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_slides_no_sentinel() {
        let text = b"ababcabcabba";
        let sa = [11, 0, 8, 5, 2, 10, 1, 9, 6, 3, 7, 4];
        assert_eq!(*sais_impl::<_, usize>(text, A), sa);
        assert_sais_eq!((text, A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_all_a_with_sentinel() {
        let text = b"aaaaaaaa\0";
        let sa = [8, 7, 6, 5, 4, 3, 2, 1, 0];
        assert_eq!(*sais_impl::<_, usize>(text, A), sa);
        assert_sais_eq!((text, A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_all_a_no_sentinel() {
        let text = b"aaaaaaaa";
        let sa = [7, 6, 5, 4, 3, 2, 1, 0];
        assert_eq!(*sais_impl::<_, usize>(text, A), sa);
        assert_sais_eq!((text, A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_null_character() {
        let text = b"aba\0cabcabba";
        let sa = [3, 11, 2, 0, 8, 5, 10, 1, 9, 6, 7, 4];
        assert_eq!(*sais_impl::<_, usize>(text, A), sa);
        assert_sais_eq!((text, A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_lorem_ipsum() {
        let text = b"Lorem ipsum dolor sit amet, qui minim labore adipisicing \
                   minim sint cillum sint consectetur cupidatat.";
        let sa = &*sa::naive(text).0;
        assert_eq!(*sais_impl::<_, usize>(text, A), *sa);
        assert_sais_eq!((text, A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_lorem_ipsum_long() {
        let text = LOREM_IPSUM_LONG;
        let sa = &*sa::naive(text).0;
        assert_eq!(*sais_impl::<_, usize>(text, A), *sa);
        assert_sais_eq!((text, A), &sa, u16, u32, u64,);
    }

    #[test]
    #[should_panic]
    fn test_sais_lorem_ipsum_long_panick() {
        let text = LOREM_IPSUM_LONG;
        let sa = &*sa::naive::<_, usize>(text).0;
        assert_eq!(*sais_impl::<_, u8>(text, A), *convert(sa));
    }


    #[test]
    fn test_sais_dna() {
        let text = b"CAACAACAAAT";
        let sa = &*sa::naive(text).0;
        assert_eq!(*sais_impl::<_, usize>(text, A), *sa);
        assert_sais_eq!((text, A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_dna_2() {
        let text = b"TGTGGGACTGTGGAG";
        let sa = &*sa::naive(text).0;
        assert_eq!(*sais_impl::<_, usize>(text, A), *sa);
        assert_sais_eq!((text, A), &sa, u8, u16, u32, u64,);
    }
}
