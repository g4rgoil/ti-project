use std::iter::zip;

use crate::suffix_array as sa;
use crate::TextExt;

pub type LCPArray = Box<[usize]>;

pub fn naive<T: Ord>(text: &[T], sa: &[usize]) -> LCPArray {
    assert_eq!(text.len(), sa.len(),);

    let mut lcp = Vec::with_capacity(text.len());
    lcp.extend(text.first().map(|_| 0));

    lcp.extend(zip(sa, sa.iter().skip(1)).map(|(i, j)| {
        let suffix_i = text.suffix(*i);
        let suffix_j = text.suffix(*j);
        common_prefix(suffix_i, suffix_j)
    }));

    lcp.into_boxed_slice()
}

pub fn kasai<T: Ord>(text: &[T], sa: &[usize], isa: &[usize]) -> LCPArray {
    assert_eq!(text.len(), sa.len());

    let mut lcp = vec![0; text.len()];

    let mut l = 0;
    for (i, &isa_i) in isa.iter().enumerate() {
        if isa_i != 0 {
            let j = sa[isa_i - 1];
            let suffix_i_l = text.suffix(i + l);
            let suffix_j_l = text.suffix(j + l);
            l += common_prefix(suffix_i_l, suffix_j_l);

            lcp[isa_i] = l;
            l = l.saturating_sub(1);
        }
    }

    lcp.into_boxed_slice()
}

pub fn phi<T: Ord>(text: &[T], sa: &[usize]) -> LCPArray {
    let mut phi = sa::phi(sa);

    let mut l = 0;

    for i in 0..sa.len() {
        let j = phi[i];
        let suffix_i_l = text.suffix(i + l);
        let suffix_j_l = text.suffix(j + l);
        l += common_prefix(suffix_i_l, suffix_j_l);

        phi[i] = l;
        l = l.saturating_sub(1);
    }

    sa.iter().map(|&sa_i| phi[sa_i]).collect()
}

fn common_prefix<T: Ord>(lhs: &[T], rhs: &[T]) -> usize {
    zip(lhs, rhs).take_while(|(l, r)| l == r).count()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_empty_text() {
        assert_eq!(*naive(b"", &[]), []);
        assert_eq!(*kasai(b"", &[], &[]), []);
        assert_eq!(*phi(b"", &[]), []);
    }

    #[test]
    fn test_simple_text() {
        let text = b"banana";
        let sa = [5, 3, 1, 0, 4, 2];
        let isa = [3, 2, 5, 1, 4, 0];
        let lcp = [0, 1, 3, 0, 0, 2];

        assert_eq!(*naive(text, &sa), lcp);
        assert_eq!(*kasai(text, &sa, &isa), lcp);
        assert_eq!(*phi(text, &sa), lcp);
    }
}
