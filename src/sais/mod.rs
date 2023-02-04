mod bucket;
mod imp;

use self::alphabet::*;
use self::index::{Index, SignedIndex};
use crate::suffix_array::result::MemoryResult;
use crate::{num::*, sa, text::Text};

pub(super) fn sais<Idx: Index>(text: &Text<u8>) -> sa::Result<u8, Idx>
where
    Idx::Signed: SignedIndex, // TODO this is bad
{
    if text.len() <= Idx::Signed::MAX.as_() {
        let mut memory = text.len() * std::mem::size_of::<Idx>();
        let mut sa = vec![zero(); text.len()].into_boxed_slice();

        memory += imp::sais_impl::<_, Idx::Signed>(text, &mut sa, ByteAlphabet);

        debug_assert!(sa.iter().all(|i| !i.is_negative()));

        // TODO Safety
        let sa = unsafe {
            let box_sa = Box::from_raw(Box::into_raw(sa) as _);
            sa::SuffixArray::new_unchecked(text, box_sa)
        };

        Ok(MemoryResult { value: sa, memory })
    } else {
        Err(sa::Error::IndexTooSmall { len: text.len(), cap: Idx::Signed::MAX.as_() })
    }
}


pub mod index {
    use std::ops::Not;

    use crate::num::*;


    // TODO this should be moved to a top level module with ArrayIndex
    pub trait Index: ArrayIndex + IntegerTypes + Transmutable<Self::Signed>
    where
        Self::Signed: SignedIndex,
    {
    }

    impl<T: ArrayIndex + IntegerTypes + Transmutable<Self::Signed>> Index for T where
        Self::Signed: SignedIndex
    {
    }

    // pointers of type Self can be safely cast to pointers of type T
    pub unsafe trait Transmutable<T>: Sized {}

    #[doc(hidden)]
    macro_rules! impl_transmutable {
            ($( $left:ty =>  $right:ty ),*) => {
                $( unsafe impl Transmutable<$right> for $left {} )*
            };
        }

    unsafe impl<T> Transmutable<T> for T {}
    impl_transmutable!(u8 => i8, u16 => i16, u32 => i32, u64 => i64, usize => isize);
    impl_transmutable!(i8 => u8, i16 => u16, i32 => u32, i64 => u64, isize => usize);

    pub trait SignedIndex: ArrayIndex + Signed + Not<Output = Self> {}

    impl<T: ArrayIndex + Signed + Not<Output = Self>> SignedIndex for T {}
}

mod marked {
    use core::fmt;

    use super::index::SignedIndex;
    use crate::num::*;

    pub fn unmarked<T: SignedIndex>(value: T) -> MarkableIndex<T> {
        debug_assert!(!value.is_negative());
        MarkableIndex(value)
    }

    pub fn marked<T: SignedIndex>(value: T) -> MarkableIndex<T> {
        debug_assert!(!value.is_negative());
        MarkableIndex(!value)
    }

    // TODO this does not belong here
    #[derive(Clone, Copy, PartialEq, Eq)]
    #[repr(transparent)]
    pub struct MarkableIndex<T>(T);

    impl<T: SignedIndex> MarkableIndex<T> {
        #[inline(always)]
        pub fn get(&self) -> T {
            if self.0.is_negative() {
                !self.0
            } else {
                self.0
            }
        }

        #[inline(always)]
        pub fn discern(&self) -> MaybeMarked<T> {
            if self.0.is_negative() {
                MaybeMarked::Marked(!self.0)
            } else {
                MaybeMarked::Unmarked(self.0)
            }
        }
    }

    impl<T> MarkableIndex<T> {
        pub fn cast_mut_slice(slice: &mut [T]) -> &mut [Self] {
            // TODO Safety
            unsafe { &mut *(slice as *mut _ as *mut _) }
        }
    }

    impl<T: One> One for MarkableIndex<T> {
        const ONE: Self = Self(T::ONE);
    }

    impl<T: Zero> Zero for MarkableIndex<T> {
        const ZERO: Self = Self(T::ZERO);
    }

    impl<T: Limits + Zero> Limits for MarkableIndex<T> {
        const MAX: Self = Self(T::MAX);
        const MIN: Self = Self(T::ZERO);
    }


    #[derive(Debug, Clone, Copy)]
    pub enum MaybeMarked<T> {
        Unmarked(T),
        Marked(T),
    }

    impl<T> MaybeMarked<T> {
        pub fn is_marked(&self) -> bool { matches!(self, Self::Marked(_)) }

        pub fn into_inner(self) -> T {
            match self {
                MaybeMarked::Unmarked(inner) => inner,
                MaybeMarked::Marked(inner) => inner,
            }
        }
    }

    impl<T: fmt::Debug + SignedIndex> fmt::Debug for MarkableIndex<T> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self.discern() {
                MaybeMarked::Unmarked(value) => write!(f, "{:?}", value),
                MaybeMarked::Marked(value) => write!(f, "!{:?}", value),
            }
        }
    }
}


// TODO maybe move this up to suffix_array
mod alphabet {
    use std::{fmt, marker::PhantomData};

    use crate::{num::*, sa::Symbol};

    // TODO do I need this extra type?
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    #[repr(transparent)]
    pub(super) struct IndexSymbol<Idx>(pub Idx);

    impl<Idx: AsPrimitive<usize>> AsPrimitive<usize> for IndexSymbol<Idx> {
        #[inline(always)]
        fn as_(self) -> usize { self.0.as_() }
    }

    impl<Idx: Zero> Zero for IndexSymbol<Idx> {
        const ZERO: Self = Self(<Idx as Zero>::ZERO);
    }

    impl<Idx: One> One for IndexSymbol<Idx> {
        const ONE: Self = Self(<Idx as One>::ONE);
    }

    impl<Idx: Limits> Limits for IndexSymbol<Idx> {
        const MAX: Self = Self(<Idx as Limits>::MAX);
        const MIN: Self = Self(<Idx as Limits>::MIN);
    }

    impl<Idx: ArrayIndex> Symbol for IndexSymbol<Idx> {}

    pub(super) trait Alphabet: Copy {
        type Symbol: Symbol;

        fn size(&self) -> usize;
    }

    #[derive(Debug, Clone, Copy)]
    pub(super) struct ByteAlphabet;

    impl Alphabet for ByteAlphabet {
        type Symbol = u8;

        fn size(&self) -> usize { u8::MAX as usize + 1 }
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
        type Symbol = IndexSymbol<Idx>;

        fn size(&self) -> usize { self.size }
    }
}


#[cfg(test)]
mod test {
    use crate::{num::*, sa, text::Text};

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
        ($text:expr, $expected:expr, for $($index:ty),* $(,)?) => {
            $({
                let text = $crate::text::Text::from_slice($text);
                let expected: &[$index] = $expected;
                let result = $crate::sais::sais::<$index>(text);
                let sa = result.as_ref().map(|sa| sa.value.inner());

                assert_eq!(sa, Ok(expected));
            })*
        };
    }

    #[test]
    fn test_sais_wikipedia_with_sentinel() {
        assert_sais_eq!(
            b"immissiissippi\0",
            &[14, 13, 6, 0, 10, 3, 7, 2, 1, 12, 11, 5, 9, 4, 8],
            for u8, i8, u16, i16, u32, i32, u64, i64, usize, isize
        );
    }

    #[test]
    fn test_sais_slides_no_sentinel() {
        assert_sais_eq!(
            b"ababcabcabba",
            &[11, 0, 8, 5, 2, 10, 1, 9, 6, 3, 7, 4],
            for u8, i8, u16, i16, u32, i32, u64, i64, usize, isize
        );
    }

    #[test]
    fn test_sais_all_a_no_sentinel() {
        assert_sais_eq!(
            b"aaaaaaaa",
            &[7, 6, 5, 4, 3, 2, 1, 0],
            for u8, i8, u16, i16, u32, i32, u64, i64, usize, isize
        );
    }

    #[test]
    fn test_sais_lorem_ipsum() {
        let text = b"Lorem ipsum dolor sit amet, qui minim labore adipisicing \
                   minim sint cillum sint consectetur cupidatat.";
        assert_sais_eq!(
            text,
            &sa::naive(text.into()).unwrap().value.into_inner(),
            for u8, i8, u16, i16, u32, i32, u64, i64, usize, isize
        );
    }

    #[test]
    fn test_sais_lorem_ipsum_long() {
        let text = LOREM_IPSUM_LONG;
        assert_sais_eq!(
            text,
            &sa::naive(text.into()).unwrap().value.into_inner(),
            for u16, i16, u32, i32, u64, i64, usize, isize
        );
    }

    #[test]
    fn test_sais_index_limits_u8() {
        let text = &[0_u8; i8::MAX as usize];
        let expected: Box<[_]> = (0..i8::MAX as usize).rev().collect();
        let sa = super::sais::<u8>(text.into()).map(|res| res.value);
        assert!(matches!(sa.as_ref().map(|x| x.inner()), Ok(expected)));
    }

    #[test]
    fn test_sais_index_limits_i8() {
        let text = &[0_u8; i8::MAX as usize];
        let expected: Box<[_]> = (0..i8::MAX as usize).rev().collect();
        let sa = super::sais::<i8>(text.into()).map(|res| res.value);
        assert!(matches!(sa.as_ref().map(|x| x.inner()), Ok(expected)));
    }

    #[test]
    fn test_sais_index_limits_u16() {
        let text = &[0_u8; i16::MAX as usize];
        let expected: Box<[_]> = (0..i16::MAX as usize).rev().collect();
        let sa = super::sais::<u16>(text.into()).map(|res| res.value);
        assert!(matches!(sa.as_ref().map(|x| x.inner()), Ok(expected)));
    }

    #[test]
    fn test_sais_index_limits_i16() {
        let text = &[0_u8; i16::MAX as usize];
        let expected: Box<[_]> = (0..i16::MAX as usize).rev().collect();
        let sa = super::sais::<i16>(text.into()).map(|res| res.value);
        assert!(matches!(sa.as_ref().map(|x| x.inner()), Ok(expected)));
    }

    #[test]
    fn test_sais_index_to_small() {
        let text = LOREM_IPSUM_LONG;

        let err = sa::Error::IndexTooSmall { len: text.len(), cap: i8::MAX as usize };
        assert!(matches!(super::sais::<u8>(text.into()), Err(err)));
        assert!(matches!(super::sais::<i8>(text.into()), Err(err)));
    }
}
