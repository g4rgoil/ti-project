use std::iter::zip;

use self::alphabet::{Alphabet, ByteAlphabet, IntegerAlphabet};
use self::buckets::Buckets;
use self::lms::LMSIter;
use super::SuffixArray;
use crate::sa::sais::lms::lms_str_from_suffix;
use crate::TextExt;

pub(super) fn sais(text: &[u8]) -> SuffixArray { sais_impl(text, ByteAlphabet) }


// TODO return Box<[]> instead here?
fn sais_impl<A: Alphabet>(text: &[A::Symbol], alphabet: A) -> SuffixArray {
    // TODO fix this
    if text.len() == 0 {
        return SuffixArray(Box::new([]));
    } else if text.len() == 1 {
        return SuffixArray(vec![0].into_boxed_slice());
    }

    let mut sa = vec![0; text.len()];
    let mut buckets = Buckets::new(text, alphabet);

    // TODO copying the buckets entirely is not necessary
    // Put LMS-suffixes in text-order at the end of buckets
    let mut lms_buckets = buckets.clone();
    let mut foo_buckets = buckets.clone();
    let mut lms_count = 0;
    for i in LMSIter::new(text) {
        sa[lms_buckets.get_mut(text[i]).take_last()] = i;
        lms_count += 1;
    }

    // Induce partial order among LMS-substrings
    induce_l_suffixes(text, &mut sa, &mut buckets);
    induce_s_suffixes(text, &mut sa, &mut buckets);

    // Collect LMS-prefixes, sorted by LMS-substrings
    // NOTE disgregarding the last bucket here
    let mut lms_sorted = Vec::with_capacity(lms_count);
    lms_sorted.extend(
        zip(buckets.end(), lms_buckets.begin().iter().skip(1))
            .flat_map(|(&i, &j)| &sa[i..j])
            .filter(|&&i| i > 0 && text[i - 1] > text[i])  // TODO naja .....
            .copied(),
    );

    // // Write rank of LMS-substring into the suffix array
    let mut iter = lms_sorted
        .iter()
        .map(|i| (i, lms_str_from_suffix(text.suffix(*i))))
        .peekable();

    let mut rank = 0;
    while let (Some((i, prev)), next) = (iter.next(), iter.peek()) {
        sa[*i] = rank;
        if next.map_or(true, |(_, next)| &prev != next) {
            rank += 1;
        }
    }


    // TODO case distinction alphabet_size ?= text_size
    // TODO use u8, u16, u32, u64 depending on lms_count
    // TODO Move this to the alphabet trait
    let mut lms_text = vec![0; lms_sorted.len()];
    let lms_alphabet = IntegerAlphabet::new(lms_sorted.len());
    let mut lms_suffixes = lms_sorted;

    // TODO instead of using LMS iter here, zero first, and just check for non-zero
    for ((dst_symbol, dst_index), i) in (lms_text.iter_mut().rev())
        .zip(lms_suffixes.iter_mut().rev())
        .zip(LMSIter::new(text))
    {
        *dst_symbol = sa[i];
        *dst_index = i;
    }

    let SuffixArray(lms_sa) = sais_impl(&lms_text, lms_alphabet);

    sa.fill(0);

    // put the sorted LMS-suffixes at the end of the buckets
    let mut iter = lms_sa.iter();
    for (&i, &j) in zip(lms_buckets.end(), &lms_buckets.begin()[1..]) {
        for (dst, n) in zip(&mut sa[i..j], iter.by_ref()) {
            *dst = lms_suffixes[*n];
        }
    }

    induce_l_suffixes(text, &mut sa, &mut foo_buckets);
    induce_s_suffixes(text, &mut sa, &mut foo_buckets);

    SuffixArray(sa.into_boxed_slice())
}

fn induce_l_suffixes<A: Alphabet>(
    text: &[A::Symbol],
    sa: &mut [usize],
    buckets: &mut Buckets<A>,
) {
    assert_eq!(text.len(), sa.len());

    // Emulate S* suffix of guardian element
    // TODO this doesn't belong here
    if let Some(last) = text.last() {
        sa[buckets.get_mut(*last).take_first()] = sa.len() - 1;
    }

    for i in 0..sa.len() {
        if sa[i] != 0 {
            let ord = text[sa[i] - 1].cmp(&text[sa[i]]);
            let bucket = buckets.get(text[sa[i]]);

            if ord.is_gt() || (ord.is_eq() && i < bucket.begin()) {
                sa[buckets.get_mut(text[sa[i] - 1]).take_first()] = sa[i] - 1;
            }
        }
    }
}

fn induce_s_suffixes<A: Alphabet>(
    text: &[A::Symbol],
    sa: &mut [usize],
    buckets: &mut Buckets<A>,
) {
    assert_eq!(text.len(), sa.len());

    for i in (0..sa.len()).rev() {
        if sa[i] != 0 {
            let ord = text[sa[i] - 1].cmp(&text[sa[i]]);
            let bucket = buckets.get(text[sa[i]]);

            if ord.is_lt() || (ord.is_eq() && i >= bucket.begin()) {
                sa[buckets.get_mut(text[sa[i] - 1]).take_last()] = sa[i] - 1;
            }
        }
    }
}


// TODO maybe move this up to suffix_array
pub(super) mod alphabet {
    use std::fmt::Debug;

    // TODO remove debug
    pub(super) trait Symbol: Sized + Copy + Ord + Debug {
        fn min_value() -> Self;
        fn to_index(self) -> usize;
    }

    impl Symbol for u8 {
        fn to_index(self) -> usize { self.into() }

        fn min_value() -> Self { 0 }
    }

    impl Symbol for usize {
        fn to_index(self) -> usize { self }

        fn min_value() -> Self { 0 }
    }

    pub(super) trait Alphabet: Clone {
        // TODO ??? + IndexMut<usize, Output = usize> ??
        type Buckets: Clone + AsRef<[usize]> + AsMut<[usize]>;
        type Symbol: Symbol;

        fn size(&self) -> usize;

        fn buckets(&self) -> Self::Buckets;
    }

    #[derive(Debug, Clone, Copy)]
    pub(super) struct ByteAlphabet;

    impl Alphabet for ByteAlphabet {
        type Buckets = [usize; u8::MAX as usize + 1];
        type Symbol = u8;

        fn size(&self) -> usize { u8::MAX as usize + 1 }

        fn buckets(&self) -> Self::Buckets { [0; u8::MAX as usize + 1] }
    }

    #[derive(Debug, Clone, Copy)]
    pub(super) struct IntegerAlphabet {
        size: usize,
    }

    impl IntegerAlphabet {
        pub(super) fn new(size: usize) -> Self { Self { size } }
    }

    impl Alphabet for IntegerAlphabet {
        type Buckets = Vec<usize>;
        type Symbol = usize;

        fn size(&self) -> usize { self.size }

        fn buckets(&self) -> Self::Buckets { vec![0; self.size] }
    }
}

#[allow(dead_code)]
mod buckets {
    use std::{iter::zip, mem, ops::Deref};

    use super::alphabet::{Alphabet, Symbol};

    #[derive(Debug, Clone)]
    pub(super) struct Buckets<A: Alphabet> {
        alphabet: A,
        begin: A::Buckets,
        end: A::Buckets,
    }


    impl<A: Alphabet> Buckets<A> {
        pub fn new(text: &[A::Symbol], alphabet: A) -> Self {
            let mut histogram = alphabet.buckets();
            for c in text {
                histogram.as_mut()[c.to_index()] += 1;
            }

            let mut bucket_begin = alphabet.buckets();
            let sum = &mut 0;
            for (begin, n) in zip(bucket_begin.as_mut(), histogram.as_ref()) {
                *begin = mem::replace(sum, *sum + n);
            }

            // Reuse histogram for bucket ends
            let mut bucket_end = histogram;
            let mut sum = 0;
            for end in bucket_end.as_mut() {
                sum += *end;
                *end = sum;
            }

            Buckets { begin: bucket_begin, end: bucket_end, alphabet }
        }

        pub fn begin(&self) -> &[usize] { self.begin.as_ref() }

        pub fn end(&self) -> &[usize] { self.end.as_ref() }

        pub fn get(&self, symbol: A::Symbol) -> Bucket<&usize> {
            Bucket {
                begin: &self.begin.as_ref()[symbol.to_index()],
                end: &self.end.as_ref()[symbol.to_index()],
            }
        }

        pub fn get_mut(&mut self, symbol: A::Symbol) -> Bucket<&mut usize> {
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

    impl<T: Deref<Target = usize>> Bucket<T> {
        pub fn begin(&self) -> usize { *self.begin }

        pub fn end(&self) -> usize { *self.end }
    }

    impl Bucket<&mut usize> {
        pub fn take_first(&mut self) -> usize {
            mem::replace(self.begin, *self.begin + 1)
        }

        pub fn take_last(&mut self) -> usize {
            *self.end -= 1;
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
        is_s_suffix: bool,
    }

    impl<'a, S> LMSIter<'a, S> {
        pub(super) fn new(text: &'a [S]) -> Self {
            LMSIter {
                text: text.iter().enumerate().rev().peekable(),
                is_s_suffix: false,
            }
        }
    }

    impl<'a, S: Symbol> Iterator for LMSIter<'a, S> {
        type Item = usize;

        fn next(&mut self) -> Option<Self::Item> {
            let mut curr = self.text.next()?;

            while let Some(&next) = self.text.peek() {
                if self.is_s_suffix {
                    if next.1 > curr.1 {
                        self.is_s_suffix = false;
                        return Some(curr.0);
                    }
                } else {
                    self.is_s_suffix = next.1 < curr.1;
                }
                self.text.next();
                curr = next;
            }
            None
        }
    }

    pub(super) fn lms_str_from_suffix<S: Symbol>(suffix: &[S]) -> &[S] {
        let (mut prev, mut increasing, mut end) = (S::min_value(), true, 0);
        for (i, &next) in suffix.iter().enumerate() {
            if increasing {
                (prev, increasing, end) = (next, prev <= next, i);
            } else {
                if prev > next {
                    (prev, end) = (next, i);
                } else if prev < next {
                    break;
                }
            }
        }
        &suffix[..=end]
    }
}


#[cfg(test)]
mod test {
    use super::{alphabet::ByteAlphabet, *};
    use crate::suffix_array as sa;

    const A: ByteAlphabet = ByteAlphabet;

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
        assert_eq!(*sais_impl(text, A), sa);
    }

    #[test]
    fn test_sais_wikipedia_no_sentinel() {
        let text = b"immissiissippi";
        let sa = [13, 6, 0, 10, 3, 7, 2, 1, 12, 11, 5, 9, 4, 8];
        assert_eq!(*sais_impl(text, A), sa);
    }

    #[test]
    fn test_sais_slides_with_sentinel() {
        let text = b"ababcabcabba\0";
        let sa = [12, 11, 0, 8, 5, 2, 10, 1, 9, 6, 3, 7, 4];
        assert_eq!(*sais_impl(text, A), sa);
    }

    #[test]
    fn test_sais_slides_no_sentinel() {
        let text = b"ababcabcabba";
        let sa = [11, 0, 8, 5, 2, 10, 1, 9, 6, 3, 7, 4];
        assert_eq!(*sais_impl(text, A), sa);
    }

    #[test]
    fn test_sais_all_a_with_sentinel() {
        let text = b"aaaaaaaa\0";
        let sa = [8, 7, 6, 5, 4, 3, 2, 1, 0];
        assert_eq!(*sais_impl(text, A), sa);
    }

    #[test]
    fn test_sais_all_a_no_sentinel() {
        let text = b"aaaaaaaa";
        let sa = [7, 6, 5, 4, 3, 2, 1, 0];
        assert_eq!(*sais_impl(text, A), sa);
    }

    #[test]
    fn test_sais_null_character() {
        let text = b"aba\0cabcabba";
        let sa = [3, 11, 2, 0, 8, 5, 10, 1, 9, 6, 7, 4];
        assert_eq!(*sais_impl(text, A), sa);
    }

    #[test]
    fn test_sais_lorem_ipsum() {
        let text = b"Lorem ipsum dolor sit amet, qui minim labore adipisicing \
                   minim sint cillum sint consectetur cupidatat.";
        let sa = &*sa::naive(text).0;
        assert_eq!(*sais_impl(text, A), *sa);
    }

    #[test]
    fn test_sais_lorem_ipsum_long() {
        let text = b"Lorem ipsum dolor sit amet, officia excepteur ex fugiat \
                   reprehenderit enim labore culpa sint ad nisi Lorem pariatur \
                   mollit ex esse exercitation amet. Nisi anim cupidatat \
                   excepteur officia. Reprehenderit nostrud nostrud ipsum Lorem \
                   est aliquip amet voluptate voluptate dolor minim nulla est \
                   proident. Nostrud officia pariatur ut officia. Sit irure \
                   elit esse ea nulla sunt ex occaecat reprehenderit commodo \
                   officia dolor Lorem duis laboris cupidatat officia voluptate. \
                   Culpa proident adipisicing id nulla nisi laboris ex in Lorem \
                   sunt duis officia eiusmod. Aliqua reprehenderit commodo ex \
                   non excepteur duis sunt velit enim. Voluptate laboris sint \
                   cupidatat ullamco ut ea consectetur et est culpa et culpa duis.";
        let sa = &*sa::naive(text).0;
        assert_eq!(*sais_impl(text, A), *sa);
    }

    #[test]
    fn test_sais_dna() {
        let text = b"CAACAACAAAT";
        let sa = &*sa::naive(text).0;
        assert_eq!(*sais_impl(text, A), *sa);
    }

    #[test]
    #[ignore]
    fn test_sais_dna_2() {
        let text = b"TGTGGGACTGTGGAG";
        let sa = &*sa::naive(text).0;
        assert_eq!(*sais_impl(text, A), *sa);
    }
}
