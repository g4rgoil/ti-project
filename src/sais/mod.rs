//! Implementation of Suffix Array Induced sorting (SAIS).
//!
//! The main part of the implementation is located in [`imp`]. Additionally
//! required data structures and functionality are located in [`bucket`],
//! [`lms`], and [`marked`].

mod bucket;
mod imp;
mod lms;
mod marked;

use crate::cast::Transmutable;
use crate::prelude::*;
use crate::sa::alphabet::ByteAlphabet;

pub fn sais<Idx>(text: &[u8]) -> sa::SAResult<u8, Idx>
where
    Idx: ArrayIndex + IntTypes + Transmutable<Idx::Signed>,
    Idx::Signed: ArrayIndex,
{
    let (len, cap) = (text.len(), Idx::Signed::MAX.as_());
    if len <= cap {
        let mut memory = len * std::mem::size_of::<Idx>();
        let mut sa = vec![zero(); len].into_boxed_slice();

        memory += imp::sais_impl::<_, Idx::Signed>(text, &mut sa, &mut [], ByteAlphabet);

        debug_assert!(sa.iter().all(|i| !i.is_negative()));

        // Safety: The bound `Idx: Transmutable<Idx::Signed>` guarantees that
        // the cast is valid. The suffix array construction is valid, assuming
        // the implementation of SAIS is correct.
        let sa = unsafe {
            let box_sa = Box::from_raw(Box::into_raw(sa) as _);
            sa::SuffixArray::new_unchecked(text, box_sa)
        };

        Ok((memory, sa))
    } else {
        Err(sa::Error::IndexTooSmall { len, cap })
    }
}

#[cfg(test)]
mod test {
    use crate::prelude::*;

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

    macro_rules! assert_sais_eq {
        ($text:expr, $expected:expr, [$($index:ty),*]) => {
            $({
                let expected: &[$index] = $expected;
                let result = $crate::sais::sais::<$index>($text);
                let sa = result.as_ref().map(|sa| sa.1.inner());
                assert_eq!(sa, Ok(expected));
            })*
        };
    }

    #[test]
    fn test_sais_wikipedia_with_sentinel() {
        assert_sais_eq!(
            b"immissiissippi\0",
            &[14, 13, 6, 0, 10, 3, 7, 2, 1, 12, 11, 5, 9, 4, 8],
            [u8, i8, u16, i16, u32, i32, u64, i64, usize, isize]
        );
    }

    #[test]
    fn test_sais_slides_no_sentinel() {
        assert_sais_eq!(
            b"ababcabcabba",
            &[11, 0, 8, 5, 2, 10, 1, 9, 6, 3, 7, 4],
            [u8, i8, u16, i16, u32, i32, u64, i64, usize, isize]
        );
    }

    #[test]
    fn test_sais_all_a_no_sentinel() {
        assert_sais_eq!(
            b"aaaaaaaa",
            &[7, 6, 5, 4, 3, 2, 1, 0],
            [u8, i8, u16, i16, u32, i32, u64, i64, usize, isize]
        );
    }

    #[test]
    fn test_sais_lorem_ipsum() {
        let text = b"Lorem ipsum dolor sit amet, qui minim labore adipisicing \
                   minim sint cillum sint consectetur cupidatat.";
        assert_sais_eq!(
            text,
            &sa::naive(text).unwrap().1.into_inner(),
            [u8, i8, u16, i16, u32, i32, u64, i64, usize, isize]
        );
    }

    #[test]
    fn test_sais_lorem_ipsum_long() {
        let text = LOREM_IPSUM_LONG;
        assert_sais_eq!(
            text,
            &sa::naive(text).unwrap().1.into_inner(),
            [u16, i16, u32, i32, u64, i64, usize, isize]
        );
    }

    #[test]
    fn test_sais_index_limits_u8() {
        let text = &[0_u8; i8::MAX as usize];
        let expected: Box<[_]> = (0..i8::MAX as u8).rev().collect();
        let sa = super::sais::<u8>(text).unwrap().1;
        assert_eq!(sa.inner(), &*expected);
    }

    #[test]
    fn test_sais_index_limits_i8() {
        let text = &[0_u8; i8::MAX as usize];
        let expected: Box<[_]> = (0..i8::MAX).rev().collect();
        let sa = super::sais::<i8>(text).unwrap().1;
        assert_eq!(sa.inner(), &*expected);
    }

    #[test]
    fn test_sais_index_limits_u16() {
        let text = &[0_u8; i16::MAX as usize];
        let expected: Box<[_]> = (0..i16::MAX as u16).rev().collect();
        let sa = super::sais::<u16>(text).unwrap().1;
        assert_eq!(sa.inner(), &*expected);
    }

    #[test]
    fn test_sais_index_limits_i16() {
        let text = &[0_u8; i16::MAX as usize];
        let expected: Box<[_]> = (0..i16::MAX).rev().collect();
        let sa = super::sais::<i16>(text).unwrap().1;
        assert_eq!(sa.inner(), &*expected);
    }

    #[test]
    fn test_sais_index_to_small() {
        let text = LOREM_IPSUM_LONG;

        let err = sa::Error::IndexTooSmall { len: text.len(), cap: i8::MAX as usize };
        assert_eq!(super::sais::<u8>(text.into()).unwrap_err(), err);
        assert_eq!(super::sais::<i8>(text.into()).unwrap_err(), err);
    }
}
