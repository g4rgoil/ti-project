use crate::TextExt;

pub type SuffixArray = Box<[usize]>;

pub fn naive<T: Ord>(text: &[T]) -> SuffixArray {
    let mut sa: Box<_> = (0..text.len()).collect();
    sa.sort_by(|l, r| text.suffix(*l).cmp(text.suffix(*r)));
    sa
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_empty_text() {
        assert_eq!(*naive(b""), []);
    }

    #[test]
    fn test_simple_text() {
        let text = b"banana";
        let sa = [5, 3, 1, 0, 4, 2];

        assert_eq!(*naive(text), sa);
    }
}
