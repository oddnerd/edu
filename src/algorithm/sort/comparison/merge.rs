pub mod top_down {

    pub fn sort<T: Ord + Clone>(slice: &mut [T]) -> () {
        sort_with(slice, &mut slice.to_vec());
    }

    fn sort_with<T: Ord + Clone>(slice: &mut [T], auxiliary: &mut [T]) -> () {
        if slice.len() > 1 {
            let (left_aux, right_aux) = auxiliary.split_at_mut(auxiliary.len() / 2);

            let (left_slice, right_slice) = slice.split_at_mut(slice.len() / 2);

            sort_with(left_aux, left_slice);
            sort_with(right_aux, right_slice);

            let mut merger = Merge {
                first: left_aux.iter().peekable(),
                second: right_aux.iter().peekable(),
            };

            for element in &mut slice.iter_mut() {
                *element = merger.next().unwrap().clone();
            }
        }
    }

    struct Merge<T: Ord + Clone, Iter: std::iter::Iterator<Item = T>> {
        first: std::iter::Peekable<Iter>,
        second: std::iter::Peekable<Iter>,
    }

    impl<T: Ord + Clone, Iter: std::iter::Iterator<Item = T>> Iterator for Merge<T, Iter> {
        type Item = T;

        fn next(&mut self) -> Option<Self::Item> {
            if let Some(left) = self.first.peek() {
                if let Some(right) = self.second.peek() {
                    if left <= right {
                        Some(self.first.next().unwrap().clone())
                    } else {
                        Some(self.second.next().unwrap().clone())
                    }
                } else {
                    Some(self.first.next().unwrap().clone())
                }
            } else {
                if let Some(right) = self.second.next() {
                    Some(right.clone())
                } else {
                    None
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
