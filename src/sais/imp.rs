use std::iter::zip;
use std::mem;

use self::marked::{marked_if, Markable};
use crate::prelude::*;
use crate::sa::alphabet::*;
use crate::sais::bucket::*;


pub(super) fn sais_impl<A: Alphabet, Idx: ArrayIndex + Signed>(
    text: &[A::Symbol],
    sa: &mut [Idx],
    alphabet: A,
    fs: &mut [Idx],
) -> usize {
    if text.is_empty() {
        return 0;
    }

    let mut memory = 2 * alphabet.size() * mem::size_of::<Idx>();

    let mut hist = (alphabet.size() > fs.len()).then(|| {
        memory += alphabet.size() * mem::size_of::<Idx>();
        vec![zero(); alphabet.size()]
    });

    let hist = hist.as_deref_mut().unwrap_or_else(|| {
        let slice = &mut fs[..alphabet.size()];
        slice.fill(zero());
        slice
    });

    for c in text {
        hist[c.as_()] += one();
    }

    let buckets = &mut *vec![zero(); alphabet.size()];
    let lms_buckets = &mut *vec![zero(); alphabet.size()];
    let mut lms_buckets = Buckets::write(lms_buckets, hist);

    let num_lms = sort_lms_strs(text, sa, &mut lms_buckets, buckets, hist);
    let (lms, tail) = sa.split_at_mut(num_lms);

    memory += sort_lms_recursive(text, lms, tail);
    tail.fill(zero());

    induce_final_order(text, sa, lms_buckets, buckets, hist, num_lms);
    memory
}

/// Postconditions:
/// - `sa` contains all LMS suffixes in the first `num_lms` positions
/// - The suffixes are sorted by corresponding LMS substring
fn sort_lms_strs<Idx: ArrayIndex + Signed>(
    text: &[impl Symbol],
    sa: &mut [Idx],
    lms_buckets: &mut Buckets<Idx, End>,
    buckets: &mut [Idx],
    histogram: &[Idx],
) -> usize {
    let sa = Markable::cast_mut_slice(sa);
    let mut begin = Buckets::write(buckets, histogram);

    // Write LMS suffixes in text order at the end of buckets
    for lms in lms::iter_lms(text) {
        let dst = lms_buckets.take_last(text[lms]).as_();
        sa[dst] = Markable::new(lms.to_index());
    }

    // Emulate LMS suffix of guardian element
    if let &[.., lhs, rhs] = text {
        let dst = begin.take_first(rhs).as_();
        sa[dst] = marked_if(lhs < rhs, (text.len() - 1).to_index());
    }

    // Induce suffixes of type L
    for i in 0..sa.len() {
        let value = sa[i];

        if value.is_unmarked_positive() {
            let idx = value.get() - one();
            let lhs = text[idx.as_().saturating_sub(1)];
            let rhs = text[idx.as_()];

            sa[begin.take_first(rhs).as_()] = marked_if(lhs < rhs, idx);
            sa[i] = zero();
        } else {
            sa[i] = value.inverse();
        }
    }

    let mut end = Buckets::write(buckets, histogram);

    // Induce suffixes of type S
    for i in (0..sa.len()).rev() {
        let value = sa[i];
        if value.is_unmarked_positive() {
            let idx = value.get() - one();
            let lhs = text[idx.as_().saturating_sub(1)];
            let rhs = text[idx.as_()];

            sa[end.take_last(rhs).as_()] = marked_if(lhs > rhs, idx);
        }
    }

    // Compact LMS suffixes at front
    compress(sa, |idx| idx.is_marked_positive().then(|| Markable::new(idx.get())))
}


/// Preconditions:
/// - `lms` contains LMS suffies sorted by corresponding LMS substring
///
/// Postcondition:
/// - `lms` contains LMS suffixes sorted lexicographically
fn sort_lms_recursive<Idx: ArrayIndex + Signed, S: Symbol>(
    text: &[S],
    lms: &mut [Idx],
    tail: &mut [Idx],
) -> usize {
    tail.fill(zero());

    // store end of LMS substrings
    lms::iter_lms(text).fold(text.len(), |lms_end, lms_begin| {
        tail[lms_begin / 2] = lms_end.to_index();
        lms_begin + 1
    });

    // TODO could be more efficient here
    // Assign names to LMS substrings
    let (size, _) = lms.iter().fold((zero(), &[][..]), |(name, prev), begin| {
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

        lms.fill(zero());
        let memory = sais_impl::<_, Idx>(lms_text, lms, alphabet, tail);

        for (lms_begin, dst) in lms::iter_lms(text).zip(lms_text.iter_mut().rev()) {
            *dst = lms_begin.to_index();
        }

        for dst in lms.iter_mut() {
            *dst = lms_text[dst.as_()];
        }

        memory
    } else {
        0
    }
}

/// Preconditions:
/// - `sa` contains sorted LMS suffixes in first `num_lms` positions
/// - `lms_buckets` points to the beginning of LMS buckets
///
/// Postcondition:
/// - `sa` contains the suffix array for `text`
fn induce_final_order<Idx: ArrayIndex + Signed>(
    text: &[impl Symbol],
    sa: &mut [Idx],
    lms_buckets: Buckets<Idx, End>,
    buckets: &mut [Idx],
    histogram: &[Idx],
    num_lms: usize,
) {
    let mut begin = Buckets::write(buckets, histogram);

    let lms_begin = lms_buckets.iter();
    let lms_end = begin.iter().skip(1);

    // Place LMS suffixes at end of buckets
    zip(lms_begin, lms_end).rev().fold(num_lms, |mut src, (fst, lst)| {
        for dst in (fst.as_()..lst.as_()).rev() {
            src -= 1;
            sa[dst] = mem::replace(&mut sa[src], zero());
        }
        src
    });

    let sa = Markable::cast_mut_slice(sa);

    // Emulate LMS suffix of guardian element
    if let &[.., lhs, rhs] = text {
        let dst = begin.take_first(rhs).as_();
        sa[dst] = marked_if(lhs < rhs, (text.len() - 1).to_index());
    }

    // Induce suffixes of type L
    for i in 0..sa.len() {
        let value = sa[i];
        sa[i] = value.inverse();

        if value.is_unmarked_positive() {
            let idx = value.get() - one();
            let lhs = text[idx.as_().saturating_sub(1)];
            let rhs = text[idx.as_()];

            sa[begin.take_first(rhs).as_()] = marked_if(lhs < rhs, idx);
        }
    }

    let mut end = Buckets::write(buckets, histogram);

    // Induce suffixes of type S
    for i in (0..sa.len()).rev() {
        let value = sa[i];

        if value.is_unmarked_positive() {
            let idx = value.get() - one();
            let lhs = text[idx.as_().saturating_sub(1)];
            let rhs = text[idx.as_()];

            sa[end.take_last(rhs).as_()] = marked_if(lhs > rhs, idx);
        } else {
            sa[i] = Markable::new(value.get());
        }
    }
}

/// Calls `f` on every element of `slice` and moves those that return
/// [`Option::Some`] to the front of `slice`.
fn compress<T>(slice: &mut [T], mut f: impl FnMut(&T) -> Option<T>) -> usize {
    (0..slice.len()).fold(0, |i, j| match f(&slice[j]) {
        Some(value) => {
            // Safety: i <= j < slice.len()
            unsafe { *slice.get_unchecked_mut(i) = value };
            i + 1
        },
        None => i,
    })
}

mod marked {
    use crate::prelude::*;

    pub fn marked_if<T: ArrayIndex + Signed>(pred: bool, value: T) -> Markable<T> {
        debug_assert!(!value.is_negative());
        Markable(value | ((pred as usize) << (T::BITS - 1)).to_index())
    }

    #[derive(Clone, Copy, PartialEq, Eq)]
    #[repr(transparent)]
    pub struct Markable<T>(T);

    impl<T: One> One for Markable<T> {
        const ONE: Self = Self(T::ONE);
    }

    impl<T: Zero> Zero for Markable<T> {
        const ZERO: Self = Self(T::ZERO);
    }

    impl<T: ArrayIndex + Signed> Markable<T> {
        pub fn new(value: T) -> Self {
            debug_assert!(!value.is_negative());
            Self(value)
        }

        pub fn is_marked(&self) -> bool { self.0.is_negative() }

        pub fn is_marked_positive(&self) -> bool { self.inverse().0.is_positive() }

        pub fn is_unmarked_positive(&self) -> bool { self.0.is_positive() }

        pub fn get(&self) -> T { self.0 & T::MAX }

        pub fn inverse(&self) -> Self { Self(self.0 ^ T::MIN) }
    }

    impl<T> Markable<T> {
        pub fn cast_mut_slice(slice: &mut [T]) -> &mut [Self] {
            // Safety: `Markable<T>` has the same layout as `T`.
            unsafe { &mut *(slice as *mut _ as *mut _) }
        }
    }
}

mod lms {
    use std::iter::{Enumerate, Peekable, Rev};
    use std::slice;

    use crate::sa::alphabet::Symbol;

    pub fn iter_lms<S>(text: &[S]) -> LMSIter<S> {
        LMSIter { text: text.iter().enumerate().rev().peekable(), decreasing: false }
    }

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
    use crate::prelude::*;
    use crate::sais;

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

    fn sais<Idx: ArrayIndex + Signed>(text: &[u8]) -> Box<[Idx]> {
        let mut sa = vec![Idx::ZERO; text.len()].into_boxed_slice();
        let alphabet = sa::alphabet::ByteAlphabet;
        let _ = sais::imp::sais_impl::<_, Idx>(text, &mut sa, alphabet, &mut []);
        sa
    }

    #[test]
    fn test_sais_empty_text() {
        let sa = sais::<isize>(b"");
        let expected = [];

        assert_eq!(*sa, expected);
    }

    #[test]
    fn test_sais_len_1() {
        let sa = sais::<isize>(b"a");
        let expected = [0];

        assert_eq!(*sa, expected);
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
        let expected = sa::naive(text).unwrap().1.into_inner();
        assert_eq!(*sa, *expected);
    }

    #[test]
    fn test_sais_lorem_ipsum_long() {
        let text = LOREM_IPSUM_LONG;
        let sa = sais::<isize>(text);
        let expected = sa::naive(text.into()).unwrap().1.into_inner();
        assert_eq!(*sa, *expected);
    }

    #[test]
    #[should_panic]
    fn test_sais_lorem_ipsum_long_panic() { let _ = sais::<i8>(LOREM_IPSUM_LONG); }


    #[test]
    fn test_sais_dna() {
        let text = b"CAACAACAAAT";
        let sa = sais::<isize>(text);
        let expected = sa::naive(text).unwrap().1.into_inner();
        assert_eq!(*sa, *expected);
    }

    #[test]
    fn test_sais_dna_2() {
        let text = b"TGTGGGACTGTGGAG";
        let sa = sais::<isize>(text);
        let expected = sa::naive(text).unwrap().1.into_inner();
        assert_eq!(*sa, *expected);
    }

    #[test]
    fn test_sais_i8_maximum() {
        let text = &[0; 127];
        let sa = sais::<i8>(text);
        let expected = sa::naive::<_, i8>(text).unwrap().1.into_inner();
        assert_eq!(*sa, *expected);
    }
}
