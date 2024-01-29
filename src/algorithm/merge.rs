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
        }
        else if let Some(right) = self.second.next() {
            Some(right.clone())
        } else {
            None
        }
    }
}
