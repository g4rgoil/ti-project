use std::iter::{Enumerate, Peekable, Rev};
use std::slice;

use self::alphabet::{Alphabet, Symbol, U8Alphabet};
use self::buckets::Buckets;
use super::SuffixArray;
use crate::TextExt;

pub(super) fn sais(text: &[u8]) -> SuffixArray { construct(text, U8Alphabet) }

fn construct<A: Alphabet>(text: &[A::Symbol], alphabet: A) -> SuffixArray {
    let mut sa = vec![0; text.len()];

    // TODO sort these using sais
    let mut lms: Box<[_]> = LMSIter::new(text).collect();
    lms.sort_by_key(|i| text.suffix(*i));

    dbg!(lms.len() as f64 / text.len() as f64);

    let mut buckets = Buckets::new(text, alphabet);

    // put sorted LMS-suffixes at the end of buckets
    // TODO this is ugly as the night
    let mut lms_iter = lms.iter().rev().peekable();
    for (symbol, bucket_end) in buckets.end().iter().enumerate().rev() {
        let mut idx = *bucket_end;
        'inner: while let Some(&&i) = lms_iter.peek() {
            if text[i].as_usize() != symbol {
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

fn induce_l_suffixes<A: Alphabet>(
    text: &[A::Symbol],
    sa: &mut [usize],
    buckets: &mut Buckets<A>,
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


struct LMSIter<'a, S> {
    text: Peekable<Rev<Enumerate<slice::Iter<'a, S>>>>,
    is_s_suffix: bool,
}

impl<'a, S> LMSIter<'a, S> {
    fn new(text: &'a [S]) -> Self {
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

pub(super) mod alphabet {
    use std::ops::IndexMut;

    pub(super) trait Symbol: Sized + Copy + Ord {
        fn as_usize(self) -> usize;
    }

    impl Symbol for u8 {
        fn as_usize(self) -> usize { self.into() }
    }

    impl Symbol for usize {
        fn as_usize(self) -> usize { self }
    }

    pub(super) trait Alphabet {
        type Buckets: IndexMut<usize, Output = usize>
            + AsRef<[usize]>
            + AsMut<[usize]>;
        type Symbol: Symbol;

        fn size(&self) -> usize;

        fn buckets(&self) -> Self::Buckets;
    }

    pub(super) struct U8Alphabet;

    impl Alphabet for U8Alphabet {
        type Buckets = [usize; u8::MAX as usize + 1];
        type Symbol = u8;

        fn size(&self) -> usize { u8::MAX as usize + 1 }

        fn buckets(&self) -> Self::Buckets { [0; u8::MAX as usize + 1] }
    }

    pub(super) struct UsizeAlphabet {
        size: usize,
    }

    impl Alphabet for UsizeAlphabet {
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
                histogram[c.as_usize()] += 1;
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
                begin: &self.begin[symbol.as_usize()],
                end: &self.end[symbol.as_usize()],
            }
        }

        pub fn get_mut(&mut self, symbol: A::Symbol) -> Bucket<&mut usize> {
            Bucket {
                begin: &mut self.begin[symbol.as_usize()],
                end: &mut self.end[symbol.as_usize()],
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
    use super::{alphabet::U8Alphabet, *};

    const A: U8Alphabet = U8Alphabet;

    #[test]
    fn test_lms_iter_empty() {
        let mut iter = LMSIter::<u8>::new(&[]);
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
        assert_eq!(*construct(text, A), sa);
    }

    #[test]
    fn test_sais_not_terminated() {
        let text = b"banana";
        let sa = [5, 3, 1, 0, 4, 2];
        assert_eq!(*construct(text, A), sa);
    }

    #[test]
    fn test_sais_all_a() {
        let text = b"aaaaaaaa";
        let sa = [7, 6, 5, 4, 3, 2, 1, 0];
        assert_eq!(*construct(text, A), sa);
    }
}
