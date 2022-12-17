use std::iter::zip;

use self::buckets::kind::{Begin, End};
use self::{alphabet::*, buckets::*, lms::*};
use super::result::MemoryResult;
use super::SuffixArray;
use crate::index::{ArrayIndex, ToIndex};
use crate::text::Text;

pub(super) fn sais<Idx: ArrayIndex>(
    text: &Text<u8>,
) -> MemoryResult<SuffixArray<u8, Idx>> {
    assert!(text.fits_index::<Idx>());

    let MemoryResult { value: sa, memory } = sais_impl(text, ByteAlphabet);
    MemoryResult { value: SuffixArray { text, sa }, memory }
}

fn sais_impl<A: Alphabet, Idx: ArrayIndex>(
    text: &Text<A::Symbol>,
    alphabet: A,
) -> MemoryResult<Box<[Idx]>> {
    debug_assert!(text.fits_index::<Idx>());

    let mut result = MemoryResult::builder();
    if text.is_empty() {
        return result.build(Box::new([]));
    }

    // TODO don't count the suffix array it self
    result.add_values::<Idx>(text.len());
    let mut sa = vec![Idx::ZERO; text.len()].into_boxed_slice();

    // TODO this is still kinda bad
    result.add_values::<Idx>(4 * alphabet.size());
    let ref histogram = histogram(text, alphabet);
    let ref mut begin = Buckets::new(histogram, alphabet, Begin);
    let ref mut end = Buckets::new(histogram, alphabet, End);
    let (ref mut lms_begin, ref mut lms_end) = (begin.clone(), end.clone());

    sort_lms_suffixes(text, &mut sa, (begin, end), (lms_begin, lms_end))
        .add_to(&mut result);

    let (last, head) = lms_end.as_mut().split_last_mut().unwrap();
    head.clone_from_slice(&lms_begin.as_ref()[1..]);
    *last = text.len().to_index();

    induce_l_suffixes(text, &mut sa, lms_begin);
    induce_s_suffixes(text, &mut sa, lms_end);

    result.build(sa)
}

#[inline(always)]
fn sort_lms_suffixes<A: Alphabet, Idx: ArrayIndex>(
    text: &Text<A::Symbol>,
    sa: &mut [Idx],
    (begin, end): (&mut Buckets<A, Idx, Begin>, &mut Buckets<A, Idx, End>),
    (lms_begin, lms_end): (&mut Buckets<A, Idx, Begin>, &mut Buckets<A, Idx, End>),
) -> MemoryResult<()> {
    let mut result = MemoryResult::builder();

    let lms_count = LMSIter::new(text)
        .inspect(|&lms| {
            let idx: Idx = lms_end.get_mut(text[lms]).take_last();
            sa[idx.as_()] = lms.to_index();
        })
        .count();

    let mut lms_sorted =
        partial_sort_lms(text, sa, (begin, end), (lms_begin, lms_end), lms_count)
            .add_to(&mut result);

    // Write rank of LMS-substring into the suffix array
    let mut iter =
        lms_sorted.iter().map(|&i| (i, lms_str_from_suffix(&text[i..]))).peekable();

    let mut rank = Idx::ZERO;
    while let (Some((i, prev)), next) = (iter.next(), iter.peek()) {
        sa[i.as_()] = rank;
        if next.map_or(true, |(_, next)| &prev != next) {
            rank += Idx::ONE;
        }
    }

    if rank.as_() == lms_sorted.len() {
        sa.fill(Idx::ZERO);
        let mut lms_iter = lms_sorted.iter();
        for (&i, &j) in zip(lms_end.iter(), lms_begin.iter().skip(1)) {
            zip(&mut sa[i.as_()..j.as_()], lms_iter.by_ref())
                .for_each(|(dst, lms)| *dst = *lms);
        }
    } else {
        sort_lms_recursive(text, sa, lms_begin, lms_end, &mut lms_sorted)
            .add_to(&mut result);
    }

    result.build(())
}


#[inline(always)]
// TODO need to  be specific here about post conditions
fn partial_sort_lms<A: Alphabet, Idx: ArrayIndex>(
    text: &Text<A::Symbol>,
    sa: &mut [Idx],
    buckets: (&mut Buckets<A, Idx, Begin>, &mut Buckets<A, Idx, End>),
    lms_buckets: (&mut Buckets<A, Idx, Begin>, &mut Buckets<A, Idx, End>),
    lms_count: usize,
) -> MemoryResult<Box<[Idx]>> {
    let mut result = MemoryResult::builder();

    // Induce partial order among LMS-substrings
    induce_l_suffixes(text, sa, buckets.0);
    induce_s_suffixes(text, sa, buckets.1);

    let mut lms_sorted = Vec::with_capacity(lms_count);
    result.add_values::<Idx>(lms_sorted.len());

    // Collect LMS-prefixes, sorted by LMS-substrings
    lms_sorted.extend(
        zip(buckets.1.iter(), lms_buckets.0.iter().skip(1))
            .flat_map(|(&i, &j)| &sa[i.as_()..j.as_()])
            .filter(|&&i| i > Idx::ZERO && text[i - Idx::ONE] > text[i])
            .copied(),
    );

    result.build(lms_sorted.into_boxed_slice())
}

#[inline(always)]
fn sort_lms_recursive<A: Alphabet, Idx: ArrayIndex>(
    text: &Text<A::Symbol>,
    sa: &mut [Idx],
    lms_begin: &mut Buckets<A, Idx, Begin>,
    lms_end: &mut Buckets<A, Idx, End>,
    lms_sorted: &mut [Idx],
) -> MemoryResult<()> {
    let mut result = MemoryResult::builder();

    // TODO use u8, u16, u32, u64 depending on lms_count

    let mut lms_text = vec![IndexSymbol(Idx::ZERO); lms_sorted.len()];
    let lms_alphabet = IndexAlphabet::new(lms_sorted.len());

    for ((dst_symbol, dst_index), i) in (lms_text.iter_mut().rev())
        .zip(lms_sorted.iter_mut().rev())
        .zip(LMSIter::new(text))
    {
        (*dst_symbol, *dst_index) = (IndexSymbol(sa[i]), i.to_index());
    }

    sa.fill(Idx::ZERO);
    let lms_sa = sais_impl::<_, Idx>(Text::from_slice(&lms_text), lms_alphabet)
        .add_to(&mut result);

    // Put the sorted LMS-suffixes at the end of the buckets
    let mut lms_iter = lms_sa.iter();
    for (&i, &j) in zip(lms_end.iter(), lms_begin.iter().skip(1)) {
        zip(&mut sa[i.as_()..j.as_()], lms_iter.by_ref())
            .for_each(|(dst, lms)| *dst = lms_sorted[lms.as_()]);
    }

    result.build(())
}


#[inline(always)]
fn induce_l_suffixes<A: Alphabet, Idx: ArrayIndex>(
    text: &Text<A::Symbol>,
    sa: &mut [Idx],
    begin: &mut Buckets<A, Idx, Begin>,
) {
    // Emulate S* suffix of guardian element
    if let Some(last) = text.0.last() {
        let idx = begin.get_mut(*last).take_first();
        sa[idx.as_()] = (sa.len() - 1).to_index();
    }

    for i in 0..sa.len() {
        if sa[i] != Idx::ZERO {
            let text_lhs = text[sa[i] - Idx::ONE];
            let text_rhs = text[sa[i]];
            let bucket = begin.get(text_rhs);

            let ord = text_lhs.cmp(&text_rhs);
            if ord.is_gt() || (ord.is_eq() && i < bucket.index().as_()) {
                let idx = begin.get_mut(text_lhs).take_first();
                sa[idx.as_()] = sa[i] - Idx::ONE;
            }
        }
    }
}

#[inline(always)]
fn induce_s_suffixes<A: Alphabet, Idx: ArrayIndex>(
    text: &Text<A::Symbol>,
    sa: &mut [Idx],
    end: &mut Buckets<A, Idx, End>,
) {
    for i in (0..sa.len()).rev() {
        if sa[i] != Idx::ZERO {
            let text_lhs = text[sa[i] - Idx::ONE];
            let text_rhs = text[sa[i]];
            let bucket = end.get(text_rhs);

            let ord = text_lhs.cmp(&text_rhs);
            if ord.is_lt() || (ord.is_eq() && i >= bucket.index().as_()) {
                let idx = end.get_mut(text_lhs).take_last();
                sa[idx.as_()] = sa[i] - Idx::ONE;
            }
        }
    }
}


// TODO maybe move this up to suffix_array
pub(super) mod alphabet {
    use std::fmt::Debug;
    use std::marker::PhantomData;

    use crate::index::{ArrayIndex, AsPrimitive};

    pub(super) trait Symbol:
        Sized + Copy + Ord + Debug + AsPrimitive<usize>
    {
        fn min_value() -> Self;
    }

    // TODO what about i8, i16, ...

    impl Symbol for u8 {
        fn min_value() -> Self { 0 }
    }

    impl Symbol for u16 {
        fn min_value() -> Self { 0 }
    }

    impl Symbol for u32 {
        fn min_value() -> Self { 0 }
    }

    impl Symbol for u64 {
        fn min_value() -> Self { 0 }
    }

    impl Symbol for usize {
        fn min_value() -> Self { 0 }
    }

    // TODO this abstraction is bad
    #[repr(transparent)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub(super) struct IndexSymbol<Idx: ArrayIndex>(pub Idx);

    impl<Idx: ArrayIndex> AsPrimitive<usize> for IndexSymbol<Idx> {
        fn as_(self) -> usize { self.0.as_() }
    }

    impl<Idx: ArrayIndex> Symbol for IndexSymbol<Idx> {
        fn min_value() -> Self { Self(ArrayIndex::ZERO) }
    }

    pub(super) trait Alphabet: Copy {
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

mod buckets {
    use std::iter::zip;
    use std::marker::PhantomData;
    use std::mem;
    use std::ops::Deref;
    use std::slice;

    use self::kind::{Begin, BucketKind, End};
    use super::alphabet::Alphabet;
    use crate::index::{ArrayIndex, AsPrimitive};
    use crate::text::Text;

    pub(super) fn histogram<A: Alphabet, Idx: ArrayIndex>(
        text: &Text<A::Symbol>,
        alphabet: A,
    ) -> A::Buckets<Idx> {
        let mut histogram = alphabet.buckets::<Idx>();
        for c in text {
            histogram.as_mut()[c.as_()] += Idx::ONE;
        }
        histogram
    }

    #[derive(Debug, Clone)]
    pub(super) struct Buckets<A: Alphabet, Idx: ArrayIndex, K: BucketKind> {
        pub inner: A::Buckets<Idx>,
        _phantom: PhantomData<(A, K)>,
    }

    impl<A: Alphabet, Idx: ArrayIndex, K: BucketKind> AsRef<[Idx]> for Buckets<A, Idx, K> {
        fn as_ref(&self) -> &[Idx] { self.inner.as_ref() }
    }

    impl<A: Alphabet, Idx: ArrayIndex, K: BucketKind> AsMut<[Idx]> for Buckets<A, Idx, K> {
        fn as_mut(&mut self) -> &mut [Idx] { self.inner.as_mut() }
    }

    impl<A: Alphabet, Idx: ArrayIndex, K: BucketKind> Buckets<A, Idx, K> {
        pub fn new(histogram: &A::Buckets<Idx>, alphabet: A, _: K) -> Self {
            let mut inner = alphabet.buckets();

            let iter = zip(inner.as_mut(), histogram.as_ref());
            iter.fold(Idx::ZERO, |sum, (dst, n)| {
                *dst = K::next(sum, *n);
                sum + *n
            });

            Self { inner, _phantom: Default::default() }
        }

        pub fn get(&self, symbol: A::Symbol) -> Bucket<&Idx, K> {
            Bucket(&self.as_ref()[symbol.as_()], Default::default())
        }

        pub fn get_mut(&mut self, symbol: A::Symbol) -> Bucket<&mut Idx, K> {
            Bucket(&mut self.as_mut()[symbol.as_()], Default::default())
        }

        pub fn iter(&self) -> slice::Iter<Idx> { self.as_ref().iter() }
    }

    // TODO I don't really need this type anymore
    #[derive(Debug, Clone)]
    pub(super) struct Bucket<T, K: BucketKind>(T, PhantomData<K>);

    impl<Idx: ArrayIndex, T: Deref<Target = Idx>, K: BucketKind> Bucket<T, K> {
        pub fn index(&self) -> Idx { *self.0 }
    }

    impl<Idx: ArrayIndex> Bucket<&mut Idx, Begin> {
        pub fn take_first(&mut self) -> Idx { mem::replace(self.0, *self.0 + Idx::ONE) }
    }

    impl<Idx: ArrayIndex> Bucket<&mut Idx, End> {
        pub fn take_last(&mut self) -> Idx {
            *self.0 -= Idx::ONE;
            *self.0
        }
    }

    pub(super) mod kind {
        use std::ops::Add;

        #[derive(Debug, Clone, Copy)]
        pub struct Begin;

        #[derive(Debug, Clone, Copy)]
        pub struct End;

        pub trait BucketKind {
            fn next<T: Add<Output = T>>(sum: T, cnt: T) -> T;
        }

        impl BucketKind for Begin {
            fn next<T: Add<Output = T>>(sum: T, _: T) -> T { sum }
        }

        impl BucketKind for End {
            fn next<T: Add<Output = T>>(sum: T, cnt: T) -> T { sum + cnt }
        }
    }
}

mod lms {
    use std::iter::{Enumerate, Peekable, Rev};
    use std::slice;

    use super::alphabet::Symbol;
    use crate::text::Text;

    // TODO maybe remove this entirely
    pub(super) struct LMSIter<'a, S> {
        text: Peekable<Rev<Enumerate<slice::Iter<'a, S>>>>,
        decreasing: bool,
    }

    impl<'a, S> LMSIter<'a, S> {
        pub fn new(text: &'a Text<S>) -> Self {
            LMSIter { text: text.iter().enumerate().rev().peekable(), decreasing: false }
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

    pub(super) fn lms_str_from_suffix<S: Symbol>(suffix: &Text<S>) -> &Text<S> {
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
        arr.iter().map(|i| i.as_().to_index()).collect()
    }

    macro_rules! assert_sais_eq {
        (($text:expr, $alphabet:expr), $sa:expr, $($type:ty),+ $(,)?) => {
            $(
                assert_eq!(
                    *$crate::suffix_array::sais::sais_impl::<_, $type>($text, $alphabet).value,
                    *$crate::suffix_array::sais::test::convert($sa)
                );
            )+
        };
    }

    // TODO
    // #[test]
    // #[ignore]
    // fn test_lms_iter_empty() {
    //     let mut iter = lms::LMSIter::<u8>::new(&[]);
    //     assert_eq!(iter.next(), None);
    // }
    //
    // #[test]
    // #[ignore]
    // fn test_lms_iter_slides() {
    //     let iter = lms::LMSIter::new(b"ababcabcabba\0");
    //     let result: Vec<usize> = iter.collect();
    //     assert_eq!(result, &[12, 8, 5, 2]);
    // }

    #[test]
    fn test_lms_str_slides() {
        assert_eq!(&lms::lms_str_from_suffix(b"abcabcabba".into()).0, b"abca");
        assert_eq!(&lms::lms_str_from_suffix(b"abcabba".into()).0, b"abca");
        assert_eq!(&lms::lms_str_from_suffix(b"abba".into()).0, b"abba");
    }

    #[test]
    fn test_lms_str_wikipedia() {
        assert_eq!(&lms::lms_str_from_suffix(b"issiissippi".into()).0, b"issi");
        assert_eq!(&lms::lms_str_from_suffix(b"iissippi".into()).0, b"iissi");
        assert_eq!(&lms::lms_str_from_suffix(b"ippi".into()).0, b"ippi");
    }

    #[test]
    fn test_lms_str_dna() {
        assert_eq!(&lms::lms_str_from_suffix(b"AACAACAAAT".into()).0, b"AACA");
        assert_eq!(&lms::lms_str_from_suffix(b"AACAAAT".into()).0, b"AACA");
        assert_eq!(&lms::lms_str_from_suffix(b"AAAT".into()).0, b"AAAT");
    }

    #[test]
    fn test_lms_str_bug() {
        assert_eq!(&lms::lms_str_from_suffix(b"decbaedecaf".into()).0, b"decba");
        assert_eq!(&lms::lms_str_from_suffix(b"aedecaf".into()).0, b"aed");
        assert_eq!(&lms::lms_str_from_suffix(b"decaf".into()).0, b"deca");
        assert_eq!(&lms::lms_str_from_suffix(b"af".into()).0, b"af");
    }

    #[test]
    fn test_lms_str_dna_bug() {
        assert_eq!(&lms::lms_str_from_suffix(b"GTGGGACTGTGGAG".into()).0, b"GTGGGA");
        assert_eq!(&lms::lms_str_from_suffix(b"ACTGTGGAG".into()).0, b"ACTG");
        assert_eq!(&lms::lms_str_from_suffix(b"GTGGAG".into()).0, b"GTGGA");
        assert_eq!(&lms::lms_str_from_suffix(b"AG".into()).0, b"AG");
    }

    #[test]
    fn test_sais_wikipedia_with_sentinel() {
        let text = b"immissiissippi\0";
        let sa = [14, 13, 6, 0, 10, 3, 7, 2, 1, 12, 11, 5, 9, 4, 8];
        assert_eq!(*sais_impl::<_, usize>(text.into(), A).value, sa);
        assert_sais_eq!((text.into(), A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_wikipedia_no_sentinel() {
        let text = b"immissiissippi";
        let sa = [13, 6, 0, 10, 3, 7, 2, 1, 12, 11, 5, 9, 4, 8];
        assert_eq!(*sais_impl::<_, usize>(text.into(), A).value, sa);
        assert_sais_eq!((text.into(), A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_slides_with_sentinel() {
        let text = b"ababcabcabba\0";
        let sa = [12, 11, 0, 8, 5, 2, 10, 1, 9, 6, 3, 7, 4];
        assert_eq!(*sais_impl::<_, usize>(text.into(), A).value, sa);
        assert_sais_eq!((text.into(), A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_slides_no_sentinel() {
        let text = b"ababcabcabba";
        let sa = [11, 0, 8, 5, 2, 10, 1, 9, 6, 3, 7, 4];
        assert_eq!(*sais_impl::<_, usize>(text.into(), A).value, sa);
        assert_sais_eq!((text.into(), A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_all_a_with_sentinel() {
        let text = b"aaaaaaaa\0";
        let sa = [8, 7, 6, 5, 4, 3, 2, 1, 0];
        assert_eq!(*sais_impl::<_, usize>(text.into(), A).value, sa);
        assert_sais_eq!((text.into(), A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_all_a_no_sentinel() {
        let text = b"aaaaaaaa";
        let sa = [7, 6, 5, 4, 3, 2, 1, 0];
        assert_eq!(*sais_impl::<_, usize>(text.into(), A).value, sa);
        assert_sais_eq!((text.into(), A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_null_character() {
        let text = b"aba\0cabcabba";
        let sa = [3, 11, 2, 0, 8, 5, 10, 1, 9, 6, 7, 4];
        assert_eq!(*sais_impl::<_, usize>(text.into(), A).value, sa);
        assert_sais_eq!((text.into(), A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_lorem_ipsum() {
        let text = b"Lorem ipsum dolor sit amet, qui minim labore adipisicing \
                   minim sint cillum sint consectetur cupidatat.";
        let sa = sa::naive(text.into()).sa;
        assert_eq!(*sais_impl::<_, usize>(text.into(), A).value, *sa);
        assert_sais_eq!((text.into(), A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_lorem_ipsum_long() {
        let text = LOREM_IPSUM_LONG;
        let sa = sa::naive(text.into()).sa;
        assert_eq!(*sais_impl::<_, usize>(text.into(), A).value, *sa);
        assert_sais_eq!((text.into(), A), &sa, u16, u32, u64,);
    }

    #[test]
    #[should_panic]
    fn test_sais_lorem_ipsum_long_panick() {
        let text = LOREM_IPSUM_LONG;
        let sa = sa::naive::<_, usize>(text.into()).sa;
        assert_eq!(*sais_impl::<_, u8>(text.into(), A).value, *convert(&sa));
    }


    #[test]
    fn test_sais_dna() {
        let text = b"CAACAACAAAT";
        let sa = sa::naive(text.into()).sa;
        assert_eq!(*sais_impl::<_, usize>(text.into(), A).value, *sa);
        assert_sais_eq!((text.into(), A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_dna_2() {
        let text = b"TGTGGGACTGTGGAG";
        let sa = sa::naive(text.into()).sa;
        assert_eq!(*sais_impl::<_, usize>(text.into(), A).value, *sa);
        assert_sais_eq!((text.into(), A), &sa, u8, u16, u32, u64,);
    }

    #[test]
    fn test_sais_u8_maximum() {
        let text = &[0; 255];
        let sa = sa::naive(text.into()).sa;
        assert_eq!(*sais_impl::<_, usize>(text.into(), A).value, *sa);
        assert_sais_eq!((text.into(), A), &sa, u8, u16, u32, u64,);
    }
}
