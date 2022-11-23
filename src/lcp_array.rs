use std::iter::zip;

use crate::TextExt;

pub type LCPArray = Box<[usize]>;

pub fn naive<T: Ord>(text: &[T], sa: &[usize]) -> LCPArray {
    assert_eq!(text.len(), sa.len(),);

    let mut lcp = Vec::with_capacity(text.len());
    lcp.extend(text.first().map(|_| 0));

    lcp.extend(zip(sa, sa.iter().skip(1)).map(|(i, j)| {
        zip(text.suffix(*i), text.suffix(*j)).take_while(|(l, r)| l == r).count()
    }));

    lcp.into_boxed_slice()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_empty_text() {
        assert_eq!(*naive(b"", &[]), []);
    }

    #[test]
    fn test_simple_text() {
        let text = b"banana";
        let sa = [5, 3, 1, 0, 4, 2];
        let lcp = [0, 1, 3, 0, 0, 2];

        assert_eq!(*naive(text, &sa), lcp);
    }
}
