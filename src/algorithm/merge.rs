//! Combine (merge) sorted collections whilst preserving order.

/// An [`Iterator`] to traverse two other sorted [`Iterator`] in sorted order.
///
/// <div class="warning">The underlying [`Iterator`]s MUST return items in sorted order</div>
///
/// # Examples:
/// ```
/// use rust::algorithm::merge::MergeIter;
/// let first = [0,2,4];
/// let second = [1,3,5];
/// let output: Vec<_> = MergeIter::new(first.iter(), second.iter()).cloned().collect();
/// assert_eq!(output, [0,1,2,3,4,5]);
/// ```
#[derive(Debug)]
pub struct MergeIter<T: Ord, Iter: Iterator<Item = T>> {
    first: std::iter::Peekable<Iter>,
    second: std::iter::Peekable<Iter>,
}

impl<T: Ord, Iter: Iterator<Item = T>> MergeIter<T, Iter> {
    /// Construct a [`MergeIter`] from two other [`Iterator`].
    pub fn new(first: Iter, second: Iter) -> Self {
        MergeIter {
            first: first.peekable(),
            second: second.peekable(),
        }
    }
}

impl<T: Ord, Iter: Iterator<Item = T>> Iterator for MergeIter<T, Iter> {
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

#[cfg(test)]
mod mergeiter_tests {
    use super::*;

    #[test]
    fn first_empty() {
        let first = [];
        let second = [0];
        let result: Vec<&i32> = MergeIter::new(first.iter(), second.iter()).collect();

        assert_eq!(result.len(), 1);
        assert_eq!(*result[0], 0);
    }

    #[test]
    fn second_empty() {
        let first = [0];
        let second = [];
        let result: Vec<&i32> = MergeIter::new(first.iter(), second.iter()).collect();

        assert_eq!(result.len(), 1);
        assert_eq!(*result[0], 0);
    }

    #[test]
    fn first_greater() {
        let first = [1];
        let second = [0];
        let result: Vec<&i32> = MergeIter::new(first.iter(), second.iter()).collect();

        assert_eq!(result.len(), 2);
        assert_eq!(*result[0], 0);
        assert_eq!(*result[1], 1);
    }

    #[test]
    fn second_greater() {
        let first = [0];
        let second = [1];
        let result: Vec<&i32> = MergeIter::new(first.iter(), second.iter()).collect();

        assert_eq!(result.len(), 2);
        assert_eq!(*result[0], 0);
        assert_eq!(*result[1], 1);
    }

    #[test]
    fn back_and_forth() {
        let first = [1, 2];
        let second = [0, 3];
        let result: Vec<&i32> = MergeIter::new(first.iter(), second.iter()).collect();

        assert_eq!(result.len(), 4);
        assert_eq!(*result[0], 0);
        assert_eq!(*result[1], 1);
        assert_eq!(*result[2], 2);
        assert_eq!(*result[3], 3);
    }
}

/// Merge two slices into one output slice.
///
/// Peek each underlying [`Iterator`] and compare, returning the smaller
/// without consuming the other, thereby allowing it to be quired again next.
///
/// # Examples:
/// ```
/// use rust::algorithm::merge::recursive;
/// let first = [0,2,4];
/// let second = [1,3,5];
/// let mut output = [0; 6];
/// recursive(&first, &second, &mut output);
/// assert_eq!(output, [0,1,2,3,4,5]);
/// ```
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

        recursive(
            &first[..middle],
            &second[..intersect],
            &mut output[..middle + intersect],
        );
        recursive(
            &first[middle + 1..],
            &second[intersect..],
            &mut output[middle + intersect + 1..],
        );
    }
}

#[cfg(test)]
mod recursive_tests {
    use super::*;

    #[test]
    fn first_empty() {
        let first = [];
        let second = [0];
        let mut output = vec![0; 1];
        recursive(&first, &second, &mut output);

        assert_eq!(output.len(), 1);
        assert_eq!(output[0], 0);
    }

    #[test]
    fn second_empty() {
        let first = [0];
        let second = [];
        let mut output = vec![0; 1];
        recursive(&first, &second, &mut output);

        assert_eq!(output.len(), 1);
        assert_eq!(output[0], 0);
    }

    #[test]
    fn first_greater() {
        let first = [1];
        let second = [0];
        let mut output = vec![0; 2];
        recursive(&first, &second, &mut output);

        assert_eq!(output.len(), 2);
        assert_eq!(output[0], 0);
        assert_eq!(output[1], 1);
    }

    #[test]
    fn second_greater() {
        let first = [0];
        let second = [1];
        let mut output = vec![0; 2];
        recursive(&first, &second, &mut output);

        assert_eq!(output.len(), 2);
        assert_eq!(output[0], 0);
        assert_eq!(output[1], 1);
    }

    #[test]
    fn back_and_forth() {
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

/// Merge two halves of a slice in-place.
///
/// Naive implementation, n<sup>2</sup> time complexity.
///
/// # Examples
/// ```
/// use rust::algorithm::merge::inplace;
/// let mut slice = [0,2,4,1,3,5];
/// inplace(&mut slice, 3);
/// assert_eq!(slice, [0,1,2,3,4,5]);
/// ```
pub fn inplace<T>(slice: &mut [T], mut middle: usize)
where
    T: Ord,
{
    let mut left = 0;
    let mut right = middle;

    while (left < middle) && (right < slice.len()) {
        if slice[left] < slice[right] {
            left += 1;
        } else {
            slice[left..=right].rotate_right(1);
            left += 1;
            middle += 1;
            right += 1;
        }
    }
}

#[cfg(test)]
mod inplace_tests {
    use super::*;

    #[test]
    fn first_empty() {
        let mut slice = [0];
        inplace(&mut slice, 0);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn second_empty() {
        let mut slice = [0];
        inplace(&mut slice, 1);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn first_greater() {
        let mut slice = [1, 0];
        inplace(&mut slice, 1);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn second_greater() {
        let mut slice = [0, 1];
        inplace(&mut slice, 1);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn back_and_forth() {
        let mut slice = [0, 3, 1, 2];
        inplace(&mut slice, 2);
        assert_eq!(slice, [0, 1, 2, 3]);
    }
}
