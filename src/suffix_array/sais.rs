use std::iter::{Enumerate, Peekable, Rev};
use std::slice;

use self::buckets::{Buckets, U8Alphabet};
use super::SuffixArray;
use crate::TextExt;


pub(super) fn construct(text: &[u8]) -> SuffixArray {
    let mut sa = vec![0; text.len()];

    // TODO sort these using sais
    let mut lms: Box<[_]> = LMSIter::new(text).collect();
    lms.sort_by_key(|i| text.suffix(*i));

    let mut buckets = Buckets::new(text, U8Alphabet);

    // put sorted LMS-suffixes at the end of buckets
    // TODO this is ugly as the night
    let mut lms_iter = lms.iter().rev().peekable();
    for (symbol, bucket_end) in buckets.end().iter().enumerate().rev() {
        let mut idx = *bucket_end;
        'inner: while let Some(&&i) = lms_iter.peek() {
            if text[i] != symbol as u8 {
                break 'inner;
            }
            lms_iter.next();
            idx -= 1;
            sa[idx] = i;
        }
    }

    induce_l_suffixes(text, &mut sa, &mut buckets);
    induce_s_suffixes(text, &mut sa, &mut buckets);

    SuffixArray(sa.into_boxed_slice())
}

fn induce_l_suffixes(
    text: &[u8],
    sa: &mut [usize],
    buckets: &mut Buckets<U8Alphabet>,
) {
    assert_eq!(text.len(), sa.len());

    // Emulate S* suffix of guardian element
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

fn induce_s_suffixes(
    text: &[u8],
    sa: &mut [usize],
    buckets: &mut Buckets<U8Alphabet>,
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


struct LMSIter<'a> {
    text: Peekable<Rev<Enumerate<slice::Iter<'a, u8>>>>,
    is_s_suffix: bool,
}

impl<'a> LMSIter<'a> {
    fn new(text: &'a [u8]) -> LMSIter<'a> {
        LMSIter {
            text: text.iter().enumerate().rev().peekable(),
            is_s_suffix: false,
        }
    }
}

impl<'a> Iterator for LMSIter<'a> {
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

#[allow(dead_code)]
mod buckets {
    use std::{
        iter::zip,
        mem,
        ops::{Deref, IndexMut},
    };


    pub(super) trait Alphabet {
        // TODO maybe use another trait for this?!
        type Buckets: IndexMut<usize, Output = usize>
            + AsRef<[usize]>
            + AsMut<[usize]>;
        type Symbol: Sized + Copy;

        fn buckets(&self) -> Self::Buckets;

        fn as_usize(symbol: Self::Symbol) -> usize;
    }

    pub(super) struct U8Alphabet;

    impl Alphabet for U8Alphabet {
        type Buckets = [usize; u8::MAX as usize + 1];
        type Symbol = u8;

        fn buckets(&self) -> Self::Buckets { [0; u8::MAX as usize + 1] }

        fn as_usize(symbol: Self::Symbol) -> usize { symbol.into() }
    }

    pub(super) struct UsizeAlphabet {
        size: usize,
    }

    impl Alphabet for UsizeAlphabet {
        type Buckets = Vec<usize>;
        type Symbol = usize;

        fn buckets(&self) -> Self::Buckets { vec![0; self.size] }

        fn as_usize(symbol: Self::Symbol) -> usize { symbol }
    }

    #[must_use]
    pub(super) struct Buckets<A: Alphabet> {
        alphabet: A,
        begin: A::Buckets,
        end: A::Buckets,
    }

    impl<A: Alphabet> Buckets<A> {
        pub fn new(text: &[A::Symbol], alphabet: A) -> Self {
            let mut histogram = alphabet.buckets();
            for c in text {
                histogram[A::as_usize(*c)] += 1;
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

        pub fn get(&self, symbol: u8) -> Bucket<&usize> {
            Bucket {
                begin: &self.begin[symbol as usize],
                end: &self.end[symbol as usize],
            }
        }

        pub fn get_mut(&mut self, symbol: u8) -> Bucket<&mut usize> {
            Bucket {
                begin: &mut self.begin[symbol as usize],
                end: &mut self.end[symbol as usize],
            }
        }
    }

    #[must_use]
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


#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_lms_iter_empty() {
        let mut iter = LMSIter::new(&[]);
        assert_eq!(iter.next(), None);
    }

    #[test]
    #[ignore]
    fn test_lms_iter_slides() {
        let iter = LMSIter::new(b"ababcabcabba\0");
        let result: Vec<usize> = iter.collect();
        assert_eq!(result, &[12, 8, 5, 2]);
    }

    #[test]
    fn test_sais_null_terminated() {
        let text = b"ababcabcabba\0";
        let sa = [12, 11, 0, 8, 5, 2, 10, 1, 9, 6, 3, 7, 4];
        assert_eq!(*construct(text), sa);
    }

    #[test]
    fn test_sais_not_terminated() {
        let text = b"banana";
        let sa = [5, 3, 1, 0, 4, 2];
        assert_eq!(*construct(text), sa);
    }

    #[test]
    fn test_sais_all_a() {
        let text = b"aaaaaaaa";
        let sa = [7, 6, 5, 4, 3, 2, 1, 0];
        assert_eq!(*construct(text), sa);
    }
}
