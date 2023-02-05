use std::iter::zip;
use std::mem;

use crate::prelude::*;
use crate::sa::alphabet::*;
use crate::sais::{bucket::*, lms, marked::*};


pub(super) fn sais_impl<A: Alphabet, Idx: ArrayIndex + Signed>(
    text: &[A::Symbol],
    sa: &mut [Idx],
    fs: &mut [Idx],
    alphabet: A,
) -> usize {
    if text.is_empty() {
        return 0;
    }

    let mut memory = 0;
    let mut alloc_buckets = || {
        memory += alphabet.size() * mem::size_of::<Idx>();
        vec![zero(); alphabet.size()]
    };

    // A best effort attempt at resuing free space in the suffix array
    let mut iter = fs.chunks_exact_mut(alphabet.size());
    let sais_memory = match (iter.next(), iter.next(), iter.next()) {
        (Some(buckets), Some(lms_buckets), Some(histogram)) => {
            histogram.fill(zero());

            sais_with_buckets(text, sa, histogram, buckets, lms_buckets)
        },
        (Some(buckets), Some(lms_buckets), _) => {
            let mut histogram = alloc_buckets();

            sais_with_buckets(text, sa, &mut histogram, buckets, lms_buckets)
        },
        (Some(buckets), ..) => {
            let mut histogram = alloc_buckets();
            let mut lms_buckets = alloc_buckets();

            sais_with_buckets(text, sa, &mut histogram, buckets, &mut lms_buckets)
        },
        _ => {
            let mut histogram = alloc_buckets();
            let mut buckets = alloc_buckets();
            let mut lms_buckets = alloc_buckets();

            sais_with_buckets(text, sa, &mut histogram, &mut buckets, &mut lms_buckets)
        },
    };
    memory + sais_memory
}

pub(super) fn sais_with_buckets<S: Symbol, Idx: ArrayIndex + Signed>(
    text: &[S],
    sa: &mut [Idx],
    histogram: &mut [Idx],
    buckets: &mut [Idx],
    lms_buckets: &mut [Idx],
) -> usize {
    for c in text {
        histogram[c.as_()] += one();
    }

    let mut lms_buckets = Buckets::new(lms_buckets, histogram);
    let num_lms = sort_lms_strs(text, sa, &mut lms_buckets, buckets, histogram);
    let (lms, tail) = sa.split_at_mut(num_lms);

    let memory = sort_lms_recursive(text, lms, tail);
    tail.fill(zero());

    induce_final_order(text, sa, lms_buckets, buckets, histogram, num_lms);
    memory
}

/// Induce a partial order among LMS suffixes.
///
/// Preconditions:
/// - `histogram` is correctly initialized for `text`
///
/// Postconditions:
/// - `sa` contains all LMS suffixes in the first `num_lms` positions
/// - The suffixes are sorted by corresponding LMS substring
/// - `lms_buckets` points to the start of LMS buckets
fn sort_lms_strs<S: Symbol, Idx: ArrayIndex + Signed>(
    text: &[S],
    sa: &mut [Idx],
    lms_buckets: &mut Buckets<Idx, End>,
    buckets: &mut [Idx],
    histogram: &[Idx],
) -> usize {
    let sa = Markable::cast_mut_slice(sa);

    // Write LMS suffixes in text order at the end of buckets
    for (lms, c) in lms::iter_lms(text) {
        sa[lms_buckets.take(*c).as_()] = Markable::new(lms.to_index());
    }

    let mut begin = Buckets::<_, Begin>::new(buckets, histogram);

    // Emulate LMS suffix of guardian element
    if let &[.., lhs, rhs] = text {
        let dst = begin.take(rhs).as_();
        sa[dst] = Markable::new((text.len() - 1).to_index()).marked_if(lhs < rhs);
    }

    // Induce suffixes of type L
    // Postcondition: Only leftmost L suffixes are in `sa`
    for i in 0..sa.len() {
        let value = sa[i];
        if value.is_unmarked_positive() {
            let idx = value.get() - one();
            let rhs = text[idx.as_()];
            let dst = begin.take(rhs);

            // Mark end of L bucket (=> `i-1` is not an L suffix)
            let lhs = text[idx.as_().saturating_sub(1)];
            sa[dst.as_()] = Markable::new(idx).marked_if(lhs < rhs);

            sa[i] = zero();
        } else {
            sa[i] = value.inverse();
        }
    }

    // Induce suffixes of type S
    let mut end = Buckets::<_, End>::new(buckets, histogram);
    for i in (0..sa.len()).rev() {
        let value = sa[i];
        if value.is_unmarked_positive() {
            let idx = value.get() - one();
            let rhs = text[idx.as_()];
            let dst = end.take(rhs);

            // Mark end of S bucket (=> `i` is S*, i-1` is not S suffix)
            let lhs = text[idx.as_().saturating_sub(1)];
            sa[dst.as_()] = Markable::new(idx).marked_if(lhs > rhs);
        }
    }

    // Compact partially sorted LMS suffixes at the front.
    compact(sa, |i| if i.is_marked_positive() { Some(i.inverse()) } else { None })
}

/// Sort LMS suffix lexicographically, potentially by recursively invoking `sais_impl`.
///
/// Preconditions:
/// - `lms` contains LMS suffies sorted by corresponding LMS substring
/// - `lms.len()` + `tail.len()` = `text.len()`
/// - `tail.len()` >= text.len() / 2
///
/// Postcondition:
/// - `lms` contains LMS suffixes sorted lexicographically.
fn sort_lms_recursive<Idx: ArrayIndex + Signed, S: Symbol>(
    text: &[S],
    lms: &mut [Idx],
    tail: &mut [Idx],
) -> usize {
    tail.fill(zero());

    // Find end of LMS substring (i.e. beginning of next LMS suffix)
    lms::iter_lms(text).fold(text.len(), |lms_end, (lms_begin, _)| {
        // Valid because `tail.len()` >= `text.len()` / 2. Also, LMS suffixes
        // are never directly consecutive, thefore `lms_begin / 2` is unique.
        tail[lms_begin / 2] = lms_end.to_index();
        lms_begin + 1
    });

    // Assign names to LMS substrings
    let (name, _) = lms.iter().fold((zero(), &[][..]), |(name, prev), begin| {
        let end = tail[begin.as_() / 2];
        let curr = &text[begin.as_()..end.as_()];
        let name = if prev == curr { name } else { name + one() };
        tail[begin.as_() / 2] = name;

        (name, curr)
    });

    // LMS substrings are not yet unique
    if name.as_() < lms.len() {
        // Compact the new text and make sure names start at zero
        compact(tail, |x| if x.is_positive() { Some(*x - one()) } else { None });

        let (lms_text, tail) = tail.split_at_mut(lms.len());
        let lms_sa = lms;
        lms_sa.fill(zero());

        let alphabet = IndexAlphabet::<Idx>::new(name.as_());
        let memory = sais_impl::<_, Idx>(lms_text, lms_sa, tail, alphabet);

        // Write LMS suffixes in text order
        for ((suffix, _), dst) in lms::iter_lms(text).zip(lms_text.iter_mut().rev()) {
            *dst = suffix.to_index();
        }

        // Finally sort LMS suffixes using the suffix array for the reduced text.
        // The result may (and will always) be non-unique.
        for dst in lms_sa.iter_mut() {
            *dst = lms_text[dst.as_()];
        }
        memory
    } else {
        0
    }
}

/// Use the sorted LMS suffixes to induce the suffix array
///
/// # Preconditions
/// - `sa` contains sorted LMS suffixes in first `num_lms` positions
/// - `lms_buckets` points to the beginning of LMS buckets
///
/// # Postcondition
/// - `sa` contains the suffix array for `text`
fn induce_final_order<S: Symbol, Idx: ArrayIndex + Signed>(
    text: &[S],
    sa: &mut [Idx],
    lms_buckets: Buckets<Idx, End>,
    buckets: &mut [Idx],
    histogram: &[Idx],
    num_lms: usize,
) {
    let mut begin = Buckets::<_, Begin>::new(buckets, histogram);
    let lms_begin = lms_buckets.inner.iter();
    let lms_end = begin.inner.iter().skip(1);

    // Place LMS suffixes at end of buckets. Use the fact that `lms_begin`
    // points to front of LMS buckets and `lms_end` to ends.
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
        let dst = begin.take(rhs).as_();
        sa[dst] = Markable::new((text.len() - 1).to_index()).marked_if(lhs < rhs);
    }

    // Induce suffixes of type L
    for i in 0..sa.len() {
        let value = sa[i];

        // To the right of the cursor only leftmost L suffixes are unmarked
        sa[i] = value.inverse();
        if value.is_unmarked_positive() {
            let idx = value.get() - one();
            let rhs = text[idx.as_()];
            let dst = begin.take(rhs);

            // Mark end of L bucket (=> `idx-1` is not an L suffix)
            let lhs = text[idx.as_().saturating_sub(1)];
            sa[dst.as_()] = Markable::new(idx).marked_if(lhs < rhs);
        }
    }

    // Induce suffixes of type S
    let mut end = Buckets::<_, End>::new(buckets, histogram);
    for i in (0..sa.len()).rev() {
        let value = sa[i];

        // Remove marks to the right of the cursor
        sa[i] = value.unmarked();
        if value.is_unmarked_positive() {
            let idx = value.get() - one();
            let rhs = text[idx.as_()];
            let dst = end.take(rhs);

            // Mark end of S bucket (=> `idx-1` is not an S suffix)
            let lhs = text[idx.as_().saturating_sub(1)];
            sa[dst.as_()] = Markable::new(idx).marked_if(lhs > rhs);
        }
    }
}

/// Calls `f` on every element of `slice`. If the function returns
/// [`Option::Some`] writes the value to the front of the slice.
fn compact<T>(slice: &mut [T], mut f: impl FnMut(&T) -> Option<T>) -> usize {
    (0..slice.len()).fold(0, |i, j| match f(&slice[j]) {
        Some(value) => {
            // Safety: i <= j < slice.len()
            unsafe { *slice.get_unchecked_mut(i) = value };
            i + 1
        },
        None => i,
    })
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
        let _ = sais::imp::sais_impl::<_, Idx>(text, &mut sa, &mut [], alphabet);
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
