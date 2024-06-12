//! Combine (merge) sorted collections whilst preserving order.

/// An [`Iterator`] to traverse two other sorted [`Iterator`] in sorted order.
///
/// # Examples
/// ```
/// use rust::algorithm::merge::Iter;
///
/// let instance = Iter::new([0, 2, 4].into_iter(), [1, 3, 5].into_iter());
///
/// assert!(instance.eq([0, 1, 2, 3, 4, 5]));
/// ```
#[derive(Debug)]
pub struct Iter<T: Ord, I: Iterator<Item = T>> {
    /// The first [`Iterator`] to merge.
    first: core::iter::Peekable<I>,

    /// The second [`Iterator`] to merge.
    second: core::iter::Peekable<I>,
}

impl<T: Ord, I: Iterator<Item = T>> Iter<T, I> {
    /// Construct an [`Iter`] from two other [`Iterator`].
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    pub fn new(first: I, second: I) -> Self {
        Iter {
            first: first.peekable(),
            second: second.peekable(),
        }
    }
}

impl<T: Ord, I: Iterator<Item = T>> Iterator for Iter<T, I> {
    type Item = T;

    /// Obtain the next item in sorted order.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::algorithm::merge::Iter;
    ///
    /// let mut instance = Iter::new(
    ///     [0, 2, 4].into_iter(),
    ///     [1, 3, 5].into_iter()
    /// );
    ///
    /// assert_eq!(instance.next(), Some(0));
    /// assert_eq!(instance.next(), Some(1));
    /// assert_eq!(instance.next(), Some(2));
    /// assert_eq!(instance.next(), Some(3));
    /// assert_eq!(instance.next(), Some(4));
    /// assert_eq!(instance.next(), Some(5));
    /// assert_eq!(instance.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        match (self.first.peek(), self.second.peek()) {
            (Some(first), Some(second)) => {
                if first <= second {
                    self.first.next()
                } else {
                    self.second.next()
                }
            }
            (Some(_), None) => self.first.next(),
            (None, Some(_)) => self.second.next(),
            (None, None) => None,
        }
    }
}

/// Merge two slices into one output slice.
///
/// This algorithm is _NOT_ stable meaning the order of equal elements
/// is _NOT_ guaranteed.
///
/// For the convenience of implementation to not depend on a particular
/// executor, this method executes synchronously within the singly calling
/// thread. However, the implementation is of a parallel algorithm that could
/// be trivially modified to execute asynchronously.
///
/// # Performance
/// Synchronous: This method takes O(N * log N) time and consumes O(N) memory.
///
/// Asynchronous: This method takes O(log<sup>2</sup> N) time and consumes
/// O(N) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::merge::parallel;
///
/// let first  = [0, 2, 4];
/// let second = [1, 3, 5];
/// let mut output = [0; 6];
///
/// parallel(&first, &second, &mut output);
///
/// assert_eq!(output, [0, 1, 2, 3, 4, 5]);
/// ```
#[allow(clippy::indexing_slicing)]
#[allow(clippy::arithmetic_side_effects)]
pub fn parallel<T: Ord + Clone>(first: &[T], second: &[T], output: &mut [T]) {
    if first.len() < second.len() {
        return parallel(second, first, output);
    }

    if first.is_empty() {
        return;
    }

    let middle = first.len() / 2;

    // NOTE: binary search is O(log N).
    let intersect = match second.binary_search(&first[middle]) {
        Err(index) | Ok(index) => index,
    };

    let (first_left, first_right) = first.split_at(middle);
    let (second_left, second_right) = second.split_at(intersect);
    let (output_left, output_right) = output.split_at_mut(middle + intersect);

    output_right[0] = first_right[0].clone();
    let output_right = &mut output_right[1..];
    let first_right = &first_right[1..];

    // The following calls could be executed concurrently.
    parallel(first_left, second_left, output_left);
    parallel(first_right, second_right, output_right);
}

/// Merge independently sorted `[..middle]` and `[middle..]` together in-place.
///
/// # Performance
/// This method takes O(N<sup>2</sup>) time and consumes O(1) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::merge::in_place;
///
/// let mut slice = [0, 2, 4, 1, 3, 5];
///
/// in_place(&mut slice, 3);
///
/// assert_eq!(slice, [0, 1, 2, 3, 4, 5]);
/// ```
#[allow(clippy::indexing_slicing)]
#[allow(clippy::arithmetic_side_effects)]
#[allow(clippy::range_plus_one)]
pub fn in_place<T: Ord>(slice: &mut [T], middle: usize) {
    let mut left = 0..middle;
    let mut right = middle..slice.len();

    while !left.is_empty() && !right.is_empty() {
        if slice[left.start] < slice[right.start] {
            _ = left.next();
        } else {
            slice[left.start..=right.start].rotate_right(1);

            left = (left.start + 1)..(left.end + 1);
            _ = right.next();
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    mod iter {
        use super::*;

        #[test]
        fn first_empty() {
            let first = [];
            let second = [0];
            let result: Vec<&i32> = Iter::new(first.iter(), second.iter()).collect();

            assert_eq!(result.len(), 1);
            assert_eq!(*result[0], 0);
        }

        #[test]
        fn second_empty() {
            let first = [0];
            let second = [];
            let result: Vec<&i32> = Iter::new(first.iter(), second.iter()).collect();

            assert_eq!(result.len(), 1);
            assert_eq!(*result[0], 0);
        }

        #[test]
        fn first_greater() {
            let first = [1];
            let second = [0];
            let result: Vec<&i32> = Iter::new(first.iter(), second.iter()).collect();

            assert_eq!(result.len(), 2);
            assert_eq!(*result[0], 0);
            assert_eq!(*result[1], 1);
        }

        #[test]
        fn second_greater() {
            let first = [0];
            let second = [1];
            let result: Vec<&i32> = Iter::new(first.iter(), second.iter()).collect();

            assert_eq!(result.len(), 2);
            assert_eq!(*result[0], 0);
            assert_eq!(*result[1], 1);
        }

        #[test]
        fn back_and_forth() {
            let first = [1, 2];
            let second = [0, 3];
            let result: Vec<&i32> = Iter::new(first.iter(), second.iter()).collect();

            assert_eq!(result.len(), 4);
            assert_eq!(*result[0], 0);
            assert_eq!(*result[1], 1);
            assert_eq!(*result[2], 2);
            assert_eq!(*result[3], 3);
        }
    }

    mod parallel {
        use super::*;

        #[test]
        fn first_empty() {
            let first = [];
            let second = [0];
            let mut output = vec![0; 1];
            parallel(&first, &second, &mut output);

            assert_eq!(output.len(), 1);
            assert_eq!(output[0], 0);
        }

        #[test]
        fn second_empty() {
            let first = [0];
            let second = [];
            let mut output = vec![0; 1];
            parallel(&first, &second, &mut output);

            assert_eq!(output.len(), 1);
            assert_eq!(output[0], 0);
        }

        #[test]
        fn first_greater() {
            let first = [1];
            let second = [0];
            let mut output = vec![0; 2];
            parallel(&first, &second, &mut output);

            assert_eq!(output.len(), 2);
            assert_eq!(output[0], 0);
            assert_eq!(output[1], 1);
        }

        #[test]
        fn second_greater() {
            let first = [0];
            let second = [1];
            let mut output = vec![0; 2];
            parallel(&first, &second, &mut output);

            assert_eq!(output.len(), 2);
            assert_eq!(output[0], 0);
            assert_eq!(output[1], 1);
        }

        #[test]
        fn back_and_forth() {
            let first = [1, 2];
            let second = [0, 3];
            let mut output = vec![0; 4];
            parallel(&first, &second, &mut output);

            assert_eq!(output.len(), 4);
            assert_eq!(output[0], 0);
            assert_eq!(output[1], 1);
            assert_eq!(output[2], 2);
            assert_eq!(output[3], 3);
        }
    }

    mod inplace {
        use super::*;

        #[test]
        fn first_empty() {
            let mut slice = [0];
            in_place(&mut slice, 0);
            assert_eq!(slice, [0]);
        }

        #[test]
        fn second_empty() {
            let mut slice = [0];
            in_place(&mut slice, 1);
            assert_eq!(slice, [0]);
        }

        #[test]
        fn first_greater() {
            let mut slice = [1, 0];
            in_place(&mut slice, 1);
            assert_eq!(slice, [0, 1]);
        }

        #[test]
        fn second_greater() {
            let mut slice = [0, 1];
            in_place(&mut slice, 1);
            assert_eq!(slice, [0, 1]);
        }

        #[test]
        fn back_and_forth() {
            let mut slice = [0, 3, 1, 2];
            in_place(&mut slice, 2);
            assert_eq!(slice, [0, 1, 2, 3]);
        }
    }
}
