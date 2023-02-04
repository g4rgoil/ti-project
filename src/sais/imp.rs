use core::slice;
use std::any::Any;
use std::iter::zip;
use std::mem;

use self::lms::{iter_lms, LMSIter};
use super::bucket::kind::{BucketKind, Invalid};
use super::index::SignedIndex;
use crate::num::{one, zero, ArrayIndex, ToIndex};
use crate::sa::Symbol;
use crate::sais::bucket::kind::{Begin, End};
use crate::sais::marked::{marked, unmarked, MarkableIndex, MaybeMarked::*};
use crate::sais::{
    alphabet::{self, *},
    bucket::*,
};
use crate::text::Text;

pub(super) fn sais_impl<A: Alphabet, Idx: SignedIndex>(
    text: &Text<A::Symbol>,
    sa: &mut [Idx],
    alphabet: A,
) -> usize {
    debug_assert!(text.len() == sa.len());

    if text.is_empty() {
        return 0;
    }

    let mut memory = 2 * alphabet.size() * mem::size_of::<Idx>();
    let histogram = histogram(text, alphabet);
    let buckets = Buckets::new(alphabet);

    let (num_lms, buckets) = sort_lms_substrs(text, sa, &histogram, buckets);
    let (lms, tail) = sa.split_at_mut(num_lms);

    memory += sort_lms_recursive(text, lms, tail);
    tail.fill(zero());

    // Write sorted LMS suffixes into ends of buckets
    let mut buckets = buckets.write::<End>(&histogram);
    for i in (0..num_lms).rev() {
        let idx = buckets.take_last(text[sa[i]]).as_();
        sa[idx] = mem::replace(&mut sa[i], zero());
    }

    induce_suffixes(text, sa, &histogram, buckets);
    memory
}

#[inline(never)]
fn sort_lms_substrs<A: Alphabet, Idx: SignedIndex, K>(
    text: &Text<A::Symbol>,
    sa: &mut [Idx],
    histogram: &[Idx],
    buckets: Buckets<A, Idx, K>,
) -> (usize, Buckets<A, Idx, Invalid>) {
    // TODO this can be done more efficiently
    let sa = MarkableIndex::cast_mut_slice(sa);

    let mut end = buckets.write::<End>(histogram);

    // Write LMS suffixes in text order at the end of buckets
    for lms in iter_lms(text) {
        sa[end.take_last(text[lms]).as_()] = marked(lms.to_index());
    }

    // Induce L suffixes
    let mut buckets = end.write::<Begin>(histogram);

    // Emulate S* suffix of guardian element
    if let Some(last) = text.0.last() {
        sa[buckets.take_first(*last).as_()] = unmarked((sa.len() - 1).to_index());
    }

    for i in 0..sa.len() {
        if sa[i] != zero() {
            let &[lhs, rhs] = text.window::<2>(sa[i].get() - one());
            let ord = lhs.cmp(&rhs);

            if ord.is_gt() || (ord.is_eq() && i < buckets.get(rhs).as_()) {
                sa[buckets.take_first(lhs).as_()] = unmarked(sa[i].get() - one());
            }
        }
    }

    // Induce S suffixes
    let mut buckets = buckets.write::<End>(histogram);
    for i in (0..sa.len()).rev() {
        if sa[i].get() > one() {
            let &[lhs, mid, rhs] = text.window::<3>(sa[i].get() - one() - one());
            let ord = mid.cmp(&rhs);

            if (ord.is_lt() || (ord.is_eq() && i >= buckets.get(rhs).as_())) {
                sa[buckets.take_last(mid).as_()] = if lhs > mid {
                    marked(sa[i].get() - one())
                } else {
                    unmarked(sa[i].get() - one())
                };
            }
        }
    }

    // compact lms suffixes at front
    let num_lms = compress(sa, |value| match value.discern() {
        Marked(value) => Some(unmarked(value)),
        Unmarked(_) => None,
    });

    // Postcondition: `sa` contains all LMS suffixes in the first `num_lms` positions.
    // The suffixes are sorted lexicographically by corresponding LMS substring.
    (num_lms, buckets.invalidate())
}

#[inline(never)]
fn sort_lms_recursive<Idx: SignedIndex>(
    text: &Text<impl Symbol>,
    lms: &mut [Idx],
    tail: &mut [Idx],
) -> usize {
    tail.fill(zero());

    // store end of LMS substrings
    iter_lms(text).fold(text.len(), |lms_end, lms_begin| {
        tail[lms_begin / 2] = lms_end.to_index();
        lms_begin + 1
    });

    // TODO could be more efficient here
    // Assign names to LMS substrings
    let (size, _) = lms.iter().fold((zero(), (&[]).into()), |(name, prev), begin| {
        let end = tail[begin.as_() / 2];
        let curr = &text[begin.as_()..end.as_()];
        let name = if prev == curr { name } else { name + one() };
        tail[begin.as_() / 2] = name;

        (name, curr)
    });

    if size.as_() < lms.len() {
        let len = compress(tail, |x| x.is_positive().then(|| *x - one()));
        let (lms_text, tail) = tail.split_at_mut(len);
        let alphabet = IndexAlphabet::<Idx>::new(size.as_());

        let memory = {
            // TODO Safety
            let lms_text =
                unsafe { &*(lms_text as *const _ as *const [IndexSymbol<Idx>]) };

            // TODO move this to sais_impl instead?
            lms.fill(zero());
            sais_impl::<_, Idx>(Text::from_slice(&lms_text), lms, alphabet)
        };

        for (lms_begin, dst) in iter_lms(text).zip(lms_text.iter_mut().rev()) {
            *dst = lms_begin.to_index();
        }

        for dst in lms.iter_mut() {
            *dst = lms_text[dst.as_()];
        }

        memory
    } else {
        0
    }

    // Postcondition: `lms` contains LMS suffixes sorted lexicographically
}

#[inline(never)]
fn induce_suffixes<A: Alphabet, Idx: ArrayIndex, K>(
    text: &Text<A::Symbol>,
    sa: &mut [Idx],
    histogram: &[Idx],
    buckets: Buckets<A, Idx, K>,
) {
    let mut buckets = buckets.write::<Begin>(histogram);

    // Emulate S* suffix of guardian element
    if let Some(last) = text.0.last() {
        sa[buckets.take_first(*last).as_()] = (sa.len() - 1).to_index();
    }

    // Induce kind L suffixes
    for i in 0..sa.len() {
        if sa[i] != zero() {
            let &[text_lhs, text_rhs] = text.window::<2>(sa[i] - one());
            let ord = text_lhs.cmp(&text_rhs);

            if ord.is_gt() || (ord.is_eq() && i < buckets.get(text_rhs).as_()) {
                sa[buckets.take_first(text_lhs).as_()] = sa[i] - one();
            }
        }
    }

    let mut buckets = buckets.write::<End>(histogram);

    // Induce kind S suffixes
    for i in (0..sa.len()).rev() {
        if sa[i] != zero() {
            let &[text_lhs, text_rhs] = text.window::<2>(sa[i] - one());
            let ord = text_lhs.cmp(&text_rhs);

            if ord.is_lt() || (ord.is_eq() && i >= buckets.get(text_rhs).as_()) {
                sa[buckets.take_last(text_lhs).as_()] = sa[i] - one();
            }
        }
    }
}

/// Calls `f` on every element of `slice` and moves those that return
/// [`Option::Some`] to the front of `slice`.
#[inline(always)]
fn compress<T>(slice: &mut [T], mut f: impl FnMut(&T) -> Option<T>) -> usize {
    (0..slice.len()).fold(0, |i, j| match f(&slice[j]) {
        Some(value) => {
            slice[i] = value;
            i + 1
        },
        None => i,
    })
}

mod lms {
    use std::iter::{Enumerate, Peekable, Rev};
    use std::slice;

    use crate::suffix_array::Symbol;
    use crate::text::Text;

    pub fn iter_lms<S>(text: &Text<S>) -> LMSIter<S> {
        LMSIter { text: text.iter().enumerate().rev().peekable(), decreasing: false }
    }

    // TODO maybe remove this entirely
    pub struct LMSIter<'a, S> {
        text: Peekable<Rev<Enumerate<slice::Iter<'a, S>>>>,
        decreasing: bool,
    }

    impl<'a, S: Symbol> Iterator for LMSIter<'a, S> {
        type Item = usize;

        #[inline(always)]
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
}

#[cfg(test)]
mod test {
    use super::{alphabet::ByteAlphabet, *};
    use crate::{num::*, sa, sais::imp, text::Text};

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

    fn sais<Idx: SignedIndex>(text: &[u8]) -> Box<[Idx]> {
        let text = Text::from_slice(text);
        let mut sa = vec![Idx::ZERO; text.len()].into_boxed_slice();
        let _ = imp::sais_impl::<_, Idx>(text, &mut sa, A);
        sa
    }

    #[test]
    fn test_sais_wikipedia_with_sentinel() {
        let sa = sais::<isize>(b"immissiissippi\0");
        let expected = [14, 13, 6, 0, 10, 3, 7, 2, 1, 12, 11, 5, 9, 4, 8];

        assert_eq!(*sa, expected);
    }

    #[test]
    fn test_sais_wikipedia_no_sentinel() {
        let sa = sais::<isize>(b"immissiissippi");
        let expected = [13, 6, 0, 10, 3, 7, 2, 1, 12, 11, 5, 9, 4, 8];
        assert_eq!(*sa, expected);
    }

    #[test]
    fn test_sais_slides_with_sentinel() {
        let sa = sais::<isize>(b"ababcabcabba\0");
        let expected = [12, 11, 0, 8, 5, 2, 10, 1, 9, 6, 3, 7, 4];
        assert_eq!(*sa, expected);
    }

    #[test]
    fn test_sais_slides_no_sentinel() {
        let sa = sais::<isize>(b"ababcabcabba");
        let expected = [11, 0, 8, 5, 2, 10, 1, 9, 6, 3, 7, 4];
        assert_eq!(*sa, expected);
    }

    #[test]
    fn test_sais_all_a_with_sentinel() {
        let sa = sais::<isize>(b"aaaaaaaa\0");
        let expected = [8, 7, 6, 5, 4, 3, 2, 1, 0];
        assert_eq!(*sa, expected);
    }

    #[test]
    fn test_sais_all_a_no_sentinel() {
        let sa = sais::<isize>(b"aaaaaaaa");
        let expected = [7, 6, 5, 4, 3, 2, 1, 0];
        assert_eq!(*sa, expected);
    }

    #[test]
    fn test_sais_null_character() {
        let sa = sais::<isize>(b"aba\0cabcabba");
        let expected = [3, 11, 2, 0, 8, 5, 10, 1, 9, 6, 7, 4];
        assert_eq!(*sa, expected);
    }

    #[test]
    fn test_sais_lorem_ipsum() {
        let text = b"Lorem ipsum dolor sit amet, qui minim labore adipisicing \
                   minim sint cillum sint consectetur cupidatat.";
        let sa = sais::<isize>(text);
        let expected = sa::naive(text.into()).unwrap().value.into_inner();
        assert_eq!(*sa, *expected);
    }

    #[test]
    fn test_sais_lorem_ipsum_long() {
        let text = LOREM_IPSUM_LONG;
        let sa = sais::<isize>(text);
        let expected = sa::naive(text.into()).unwrap().value.into_inner();
        assert_eq!(*sa, *expected);
    }

    #[test]
    #[should_panic]
    fn test_sais_lorem_ipsum_long_panic() { let sa = sais::<i8>(LOREM_IPSUM_LONG); }


    #[test]
    fn test_sais_dna() {
        let text = b"CAACAACAAAT";
        let sa = sais::<isize>(text);
        let expected = sa::naive(text.into()).unwrap().value.into_inner();
        assert_eq!(*sa, *expected);
    }

    #[test]
    fn test_sais_dna_2() {
        let text = b"TGTGGGACTGTGGAG";
        let sa = sais::<isize>(text);
        let expected = sa::naive(text.into()).unwrap().value.into_inner();
        assert_eq!(*sa, *expected);
    }

    #[test]
    fn test_sais_i8_maximum() {
        let text = &[0; 127];
        let sa = sais::<i8>(text);
        let expected = sa::naive::<_, i8>(text.into()).unwrap().value.into_inner();
        assert_eq!(*sa, *expected);
    }
}
