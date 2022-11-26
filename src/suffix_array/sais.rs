use std::iter::{once, Enumerate, Peekable, Rev};
use std::ops::Deref;
use std::{mem, slice};

use super::SuffixArray;
use crate::TextExt;

// todo replace with const generic on Buckets
pub(super) const ALPHABET_SIZE: usize = u8::MAX as usize + 1;

pub(super) fn construct(text: &[u8]) -> SuffixArray {
    let mut sa = vec![0; text.len()];

    // TODO sort these using sais
    let mut lms: Box<[_]> = LMSIter::new(text).collect();
    lms.sort_by_key(|i| text.suffix(*i));

    let mut buckets = Buckets::new(text);

    // put sorted LMS-suffixes at the end of buckets
    // TODO this is ugly as the night
    let mut lms_iter = lms.iter().rev().peekable();
    for (symbol, bucket_end) in buckets.end.iter().enumerate().rev() {
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

    // TODO remove
    // debug_assert!(is_valid_suffix_array(text, &sa));
    SuffixArray(sa.into_boxed_slice())
}

fn induce_l_suffixes(text: &[u8], sa: &mut [usize], buckets: &mut Buckets) {
    assert_eq!(text.len(), sa.len());

    if let Some(last) = text.last() {
        sa[buckets.take_l_index(*last)] = sa.len() - 1;
    }

    for i in 0..sa.len() {
        if sa[i] != 0 {
            let is_l_type = text[sa[i] - 1] > text[sa[i]]
                || (text[sa[i] - 1] == text[sa[i]]
                    && i < buckets.begin[text[sa[i]] as usize]);

            if is_l_type {
                sa[buckets.take_l_index(text[sa[i] - 1])] = sa[i] - 1;
            }
        }
    }
}

fn induce_s_suffixes(text: &[u8], sa: &mut [usize], buckets: &mut Buckets) {
    assert_eq!(text.len(), sa.len());

    for i in (0..sa.len()).rev() {
        if sa[i] != 0 {
            let is_s_type = text[sa[i] - 1] < text[sa[i]]
                || (text[sa[i] - 1] == text[sa[i]]
                    && i >= buckets.begin[text[sa[i]] as usize]);

            if is_s_type {
                sa[buckets.take_s_index(text[sa[i] - 1])] = sa[i] - 1;
            }
        }
    }
}

struct Buckets {
    begin: [usize; ALPHABET_SIZE],
    end: [usize; ALPHABET_SIZE],
}

impl Buckets {
    pub fn new(text: &[u8]) -> Self {
        let mut histogram = [0_usize; ALPHABET_SIZE];
        for c in text {
            histogram[*c as usize] += 1;
        }

        let sum = &mut 0;
        let bucket_start = histogram.map(|n| mem::replace(sum, *sum + n));

        // TODO reuse histogram here
        let mut sum = 0;
        let bucket_end = histogram.map(|n| {
            sum += n;
            sum
        });

        Buckets { begin: bucket_start, end: bucket_end }
    }

    pub fn take_l_index(&mut self, symbol: u8) -> usize {
        let idx = &mut self.begin[symbol as usize];
        mem::replace(idx, *idx + 1)
    }

    pub fn take_s_index(&mut self, symbol: u8) -> usize {
        let idx = &mut self.end[symbol as usize];
        *idx -= 1;
        *idx
    }
}

// TODO would this make sense?
impl Buckets {
    fn bucket(&self, symbol: u8) -> Bucket<&usize> {
        Bucket {
            begin: &self.begin[symbol as usize],
            end: &self.end[symbol as usize],
        }
    }

    fn bucket_mut(&mut self, symbol: u8) -> Bucket<&mut usize> {
        Bucket {
            begin: &mut self.begin[symbol as usize],
            end: &mut self.end[symbol as usize],
        }
    }
}

struct Bucket<T> {
    begin: T,
    end: T,
}

impl<T: Deref<Target = usize>> Bucket<T> {
    fn begin(&self) -> usize { *self.begin }

    fn end(&self) -> usize { *self.end }
}

impl Bucket<&mut usize> {
    fn take_first(&mut self) -> usize { todo!() }

    fn take_last(&mut self) -> usize { todo!() }
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

        // TODO is it ok to advance twice right away?
        while let Some(&next) = self.text.peek() {
            if self.is_s_suffix {
                if next.1 > curr.1 {
                    self.is_s_suffix = false;
                    return Some(curr.0);
                }
            } else {
                self.is_s_suffix = next.1 < curr.1;
            }
            let _ = self.text.next();
            curr = next;
        }
        None
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
