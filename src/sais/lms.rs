use std::{iter, mem, slice};

/// Return an iterator of the LMS suffixes of `text` from right to left.
pub fn iter_lms<T: Ord>(text: &[T]) -> LMSIter<T> {
    LMSIter { iter: text.iter().enumerate().rev(), prev: text.last() }
}

/// An iterator over the LMS suffixes of a text. Note that the implemenation
/// always iterates back to front. This `struct` is created by [`iter_lms`].
pub struct LMSIter<'a, T> {
    iter: iter::Rev<iter::Enumerate<slice::Iter<'a, T>>>,
    prev: Option<&'a T>,
}

impl<'a, T: Ord> Iterator for LMSIter<'a, T> {
    type Item = (usize, &'a T);

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if let Some(ref mut prev) = self.prev {
            for (_, next) in self.iter.by_ref() {
                if next < mem::replace(prev, next) {
                    break;
                }
            }
            for (i, next) in self.iter.by_ref() {
                let prev = mem::replace(prev, next);
                if next > prev {
                    return Some((i + 1, prev));
                }
            }
            self.prev = None;
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) { (0, Some(self.iter.len() / 2)) }
}

#[cfg(test)]
mod test {
    use super::iter_lms;

    fn assert_lms_eq<T: Ord + PartialEq>(text: &[T], idxs: &[usize]) {
        assert!(iter_lms(text).eq(idxs.iter().rev().map(|&i| (i, &text[i]))))
    }

    #[test]
    fn test_short_texts() {
        assert_lms_eq(b"", &[]);
        assert_lms_eq(b"a", &[]);
        assert_lms_eq(b"ab", &[]);
        assert_lms_eq(b"bab", &[1]);
    }

    #[test]
    fn test_simple_text() { assert_lms_eq(b"banana", &[1, 3]) }

    #[test]
    fn test_slides() { assert_lms_eq(b"ababcabcabba", &[2, 5, 8]) }

    #[test]
    fn test_slides_with_sentinel() { assert_lms_eq(b"ababcabcabba\0", &[2, 5, 8]) }

    #[test]
    fn test_wikipedia() { assert_lms_eq(b"immissiissippi", &[3, 6, 10]) }

    #[test]
    fn test_wikipedia_with_sentinel() { assert_lms_eq(b"immissiissippi\0", &[3, 6, 10]) }

    #[test]
    fn test_all_a() { assert_lms_eq(b"aaaaaaaaaa", &[]) }
}
