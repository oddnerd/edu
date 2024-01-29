pub struct MergeIter<T: Ord, Iter: std::iter::Iterator<Item = T>> {
    first: std::iter::Peekable<Iter>,
    second: std::iter::Peekable<Iter>,
}

impl<T: Ord, Iter: std::iter::Iterator<Item = T>> MergeIter<T, Iter> {
    pub fn new(first: Iter, second: Iter) -> Self {
        MergeIter {
            first: first.peekable(),
            second: second.peekable(),
        }
    }
}

impl<T: Ord, Iter: std::iter::Iterator<Item = T>> Iterator for MergeIter<T, Iter> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(left) = self.first.peek() {
            if let Some(right) = self.second.peek() {
                if left <= right {
                    self.first.next()
                } else {
                    self.second.next()
                }
            } else {
                self.first.next()
            }
        } else {
            self.second.next()
        }
    }
}

pub fn recursive<T>(first: &[T], second: &[T], output: &mut [T])
where
    T: Ord + Clone,
{
    if first.len() < second.len() {
        return recursive(second, first, output);
    }

    if !first.is_empty() {
        let middle = first.len() / 2;
        let intersect = match second.binary_search(&first[middle]) {
            Ok(index) => index,
            Err(index) => index,
        };

        output[middle + intersect] = first[middle].clone();

        recursive(&first[..middle], &second[..intersect], &mut output[..middle + intersect]);
        recursive(&first[middle + 1..], &second[intersect..], &mut output[middle + intersect + 1..]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mergeiter_first_empty() {
        let first = [];
        let second = [0];
        let result: Vec<&i32> = MergeIter::new(first.iter(), second.iter()).collect();

        assert_eq!(result.len(), 1);
        assert_eq!(*result[0], 0);
    }

    #[test]
    fn mergeiter_second_empty() {
        let first = [0];
        let second = [];
        let result: Vec<&i32> = MergeIter::new(first.iter(), second.iter()).collect();

        assert_eq!(result.len(), 1);
        assert_eq!(*result[0], 0);
    }

    #[test]
    fn mergeiter_first_greater() {
        let first = [1];
        let second = [0];
        let result: Vec<&i32> = MergeIter::new(first.iter(), second.iter()).collect();

        assert_eq!(result.len(), 2);
        assert_eq!(*result[0], 0);
        assert_eq!(*result[1], 1);
    }

    #[test]
    fn mergeiter_second_greater() {
        let first = [0];
        let second = [1];
        let result: Vec<&i32> = MergeIter::new(first.iter(), second.iter()).collect();

        assert_eq!(result.len(), 2);
        assert_eq!(*result[0], 0);
        assert_eq!(*result[1], 1);
    }

    #[test]
    fn mergeiter_back_and_forth() {
        let first = [1, 2];
        let second = [0, 3];
        let result: Vec<&i32> = MergeIter::new(first.iter(), second.iter()).collect();

        assert_eq!(result.len(), 4);
        assert_eq!(*result[0], 0);
        assert_eq!(*result[1], 1);
        assert_eq!(*result[2], 2);
        assert_eq!(*result[3], 3);
    }

    #[test]
    fn recursive_first_empty() {
        let first = [];
        let second = [0];
        let mut output = vec![0; 1];
        recursive(&first, &second, &mut output);

        assert_eq!(output.len(), 1);
        assert_eq!(output[0], 0);
    }

    #[test]
    fn recursive_second_empty() {
        let first = [0];
        let second = [];
        let mut output = vec![0; 1];
        recursive(&first, &second, &mut output);

        assert_eq!(output.len(), 1);
        assert_eq!(output[0], 0);
    }

    #[test]
    fn recursive_first_greater() {
        let first = [1];
        let second = [0];
        let mut output = vec![0; 2];
        recursive(&first, &second, &mut output);

        assert_eq!(output.len(), 2);
        assert_eq!(output[0], 0);
        assert_eq!(output[1], 1);
    }

    #[test]
    fn recursive_second_greater() {
        let first = [0];
        let second = [1];
        let mut output = vec![0; 2];
        recursive(&first, &second, &mut output);

        assert_eq!(output.len(), 2);
        assert_eq!(output[0], 0);
        assert_eq!(output[1], 1);
    }

    #[test]
    fn recursive_back_and_forth() {
        let first = [1, 2];
        let second = [0, 3];
        let mut output = vec![0; 4];
        recursive(&first, &second, &mut output);

        assert_eq!(output.len(), 4);
        assert_eq!(output[0], 0);
        assert_eq!(output[1], 1);
        assert_eq!(output[2], 2);
        assert_eq!(output[3], 3);
    }
}
