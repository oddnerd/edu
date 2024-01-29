pub struct MergeIter<T: Ord + Clone, Iter: std::iter::Iterator<Item = T>> {
    first: std::iter::Peekable<Iter>,
    second: std::iter::Peekable<Iter>,
}

impl<T: Ord + Clone, Iter: std::iter::Iterator<Item = T>> MergeIter<T, Iter> {
    pub fn new(first: Iter, second: Iter) -> Self {
        MergeIter {
            first: first.peekable(),
            second: second.peekable(),
        }
    }
}

impl<T: Ord + Clone, Iter: std::iter::Iterator<Item = T>> Iterator for MergeIter<T, Iter> {
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
            self.second.next()
        }
    }
}

pub fn merge<T: Ord + Clone>(
    input: &[T],
    low: usize,
    high: usize,
    output: &mut [T],
    offset: usize,
) {
    let len = high - low + 1;
    if len == 1 {
        output[offset] = input[low].clone();
    } else {
        let mut auxiliary: Vec<T> = std::vec::Vec::with_capacity(len);

        let middle = (low + high) / 2;

        let other_middle = middle - low + 1;

        merge(input, low, middle, &mut auxiliary, 1);
        merge(input, middle + 1, high, &mut auxiliary, other_middle + 1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mergeiter_left_empty() {}

    #[test]
    fn mergeiter_right_empty() {}

    #[test]
    fn mergeiter_left_greater() {}

    #[test]
    fn mergeiter_right_greater() {}

    #[test]
    fn mergeiter_back_and_forth() {}

    #[test]
    fn recursive_left_empty() {}

    #[test]
    fn recursive_right_empty() {}

    #[test]
    fn recursive_left_greater() {}

    #[test]
    fn recursive_right_greater() {}

    #[test]
    fn recursive_back_and_forth() {}
}
