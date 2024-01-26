pub mod top_down {
    pub fn sort<T: Ord + Clone>(slice: &mut [T]) -> () {
        let mut auxiliary = slice.to_vec();
        split(slice, 0, slice.len(), &mut auxiliary);
    }

    fn split<T: Ord + Clone>(slice: &mut [T], begin: usize, end: usize, auxiliary: &mut [T]) -> () {
        if end - begin > 1 {
            let middle = (begin + end) / 2;
            split(auxiliary, begin, middle, slice);
            split(auxiliary, middle, end, slice);
            merge(slice, begin, middle, end, auxiliary);
        }
    }

    fn merge<T: Ord + Clone>(
        first: &mut [T],
        begin: usize,
        middle: usize,
        end: usize,
        second: &mut [T],
    ) -> () {
        let mut i = begin;
        let mut j = middle;
        let mut k = begin;
        while k < end {
            if i < middle && (j >= end || second[i] <= second[j]) {
                first[k] = second[i].clone();
                i += 1;
            } else {
                first[k] = second[j].clone();
                j += 1;
            }
            k += 1;
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn empty() {
            let mut data: [usize; 0] = [];
            sort(&mut data);
            assert_eq!(data, []);
        }

        #[test]
        fn one() {
            let mut data = [0];
            sort(&mut data);
            assert_eq!(data, [0]);
        }

        #[test]
        fn two() {
            let mut data = [2, 1];
            sort(&mut data);
            assert_eq!(data, [1, 2]);
        }

        #[test]
        fn multiple() {
            let mut data = [3, 2, 1];
            sort(&mut data);
            assert_eq!(data, [1, 2, 3]);
        }
    }
}
