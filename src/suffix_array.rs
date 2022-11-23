use crate::TextExt;

pub type SuffixArray = Box<[usize]>;
pub type InverseSuffixArray = Box<[usize]>;

pub fn naive<T: Ord>(text: &[T]) -> SuffixArray {
    let mut sa: Box<_> = (0..text.len()).collect();
    sa.sort_by(|l, r| text.suffix(*l).cmp(text.suffix(*r)));
    sa
}

pub fn inverse(sa: &[usize]) -> InverseSuffixArray {
    // TODO use MaybeUninit for optimization

    let mut isa = vec![0; sa.len()];
    for (i, sa_i) in sa.iter().enumerate() {
        // TODO elide bound checks
        isa[*sa_i] = i;
    }

    isa.into_boxed_slice()
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

    #[test]
    fn test_isa_empty() {
        assert_eq!(*inverse(&[]), []);
    }
}
