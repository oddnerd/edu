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
            merge(slice, begin, middle, auxiliary);
        }
    }

    fn merge<T: Ord + Clone>(
        first: &mut [T],
        begin: usize,
        middle: usize,
        second: &mut [T],
    ) -> () {
        let mut left_peekable = second[begin..middle].iter().peekable();
        let mut right_peekable = second[middle..].iter().peekable();

        for output in &mut first[begin..] {
            if let Some(left) = left_peekable.peek() {
                if let Some(right) = right_peekable.peek() {
                    if left <= right {
                        *output = left_peekable.next().unwrap().clone();
                    }
                    else {
                        *output = right_peekable.next().unwrap().clone();
                    }
                }
                else {
                    *output = left_peekable.next().unwrap().clone();
                }
            }
            else {
                if let Some(right) = right_peekable.next() {
                    *output = right.clone();
                }
                else {
                    panic!("output longer than sum of inputs")
                }
            }
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
