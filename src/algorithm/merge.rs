//! Combine (merge) sorted collections whilst preserving order.

/// Merge two sorted slices into one `output` slice.
///
/// # Panics
/// This method has the precondition that `output` has the _exact_ same length
/// as the sum of the input lengths.
///
/// # Performance
/// This method takes O(N) time and consumes O(1) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::merge::iterative;
///
/// let mut first  = [0, 2, 4];
/// let mut second = [1, 3, 5];
/// let mut output = [0; 6];
///
/// iterative(&mut first, &mut second, &mut output);
///
/// assert_eq!(output, [0, 1, 2, 3, 4, 5]);
/// ```
#[allow(clippy::indexing_slicing)]
pub fn iterative<T: Ord>(first: &mut [T], second: &mut [T], output: &mut [T]) {
    let Some(elements) = usize::checked_add(first.len(), second.len()) else {
        panic!("output slice cannot be big enough to store inputs");
    };

    assert_eq!(
        output.len(),
        elements,
        "output length must be sum of input lengths"
    );

    let mut first = first.iter_mut().peekable();
    let mut second = second.iter_mut().peekable();

    for element in output {
        match (first.peek_mut(), second.peek_mut()) {
            (Some(left), Some(right)) => {
                if left <= right {
                    core::mem::swap(element, *left);
                    _ = first.next();
                } else {
                    core::mem::swap(element, *right);
                    _ = second.next();
                }
            }
            (Some(left), None) => {
                core::mem::swap(element, *left);
                _ = first.next();
            }
            (None, Some(right)) => {
                core::mem::swap(element, *right);
                _ = second.next();
            }
            (None, None) => unreachable!("more output elements than input"),
        };
    }
}

/// Merge two sorted slices into one `output` slice.
///
/// This algorithm is _NOT_ stable meaning the order of equal elements
/// is _NOT_ guaranteed.
///
/// For the convenience of implementation to not depend on a particular
/// executor, this method executes synchronously within the singly calling
/// thread. However, the implementation is of a parallel algorithm that could
/// be trivially modified to execute asynchronously.
///
/// # Panics
/// This method has the precondition that `output` has the _exact_ same length
/// as the sum of the input lengths.
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
pub fn parallel<T: Ord>(first: &mut [T], second: &mut [T], output: &mut [T]) {
    let Some(elements) = usize::checked_add(first.len(), second.len()) else {
        panic!("output slice cannot be big enough to store inputs");
    };

    assert_eq!(
        output.len(),
        elements,
        "output length must be sum of input lengths"
    );

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

    let (first_left, first_right) = first.split_at_mut(middle);
    let (second_left, second_right) = second.split_at_mut(intersect);
    let (output_left, output_right) = output.split_at_mut(middle + intersect);

    core::mem::swap(&mut output_right[0], &mut first_right[0]);
    let output_right = &mut output_right[1..];
    let first_right = &mut first_right[1..];

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
#[allow(
    clippy::undocumented_unsafe_blocks,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::assertions_on_result_states,
    clippy::indexing_slicing
)]
mod test {
    use super::*;

    mod iterative {
        use super::*;

        #[test]
        fn first_empty() {
            let mut first = [];
            let mut second = [0, 1, 2, 3, 4, 5];
            let mut output = [0; 6];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn second_empty() {
            let mut first = [0, 1, 2, 3, 4, 5];
            let mut second = [];
            let mut output = [0; 6];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn both_empty() {
            let mut first = [];
            let mut second = [];
            let mut output = [0; 0];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, []);
        }

        #[test]
        fn first_longer() {
            let mut first = [0, 1, 3, 5];
            let mut second = [2, 4];
            let mut output = [0; 6];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn second_longer() {
            let mut first = [2, 4];
            let mut second = [0, 1, 3, 5];
            let mut output = [0; 6];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn first_greater() {
            let mut first = [1];
            let mut second = [0];
            let mut output = [0; 2];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1]);
        }

        #[test]
        fn second_greater() {
            let mut first = [0];
            let mut second = [1];
            let mut output = [0; 2];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1]);
        }

        #[test]
        fn back_and_forth() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [0; 6];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        #[should_panic(expected = "output length must be sum of input lengths")]
        fn output_cannot_be_smaller() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [];

            iterative(&mut first, &mut second, &mut output);
        }

        #[test]
        #[should_panic(expected = "output length must be sum of input lengths")]
        fn output_cannot_be_larger() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [0; 256];

            iterative(&mut first, &mut second, &mut output);
        }
    }

    mod parallel {
        use super::*;

        #[test]
        fn first_empty() {
            let mut first = [];
            let mut second = [0, 1, 2, 3, 4, 5];
            let mut output = [0; 6];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn second_empty() {
            let mut first = [0, 1, 2, 3, 4, 5];
            let mut second = [];
            let mut output = [0; 6];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn both_empty() {
            let mut first = [];
            let mut second = [];
            let mut output = [0; 0];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, []);
        }

        #[test]
        fn first_longer() {
            let mut first = [0, 1, 3, 5];
            let mut second = [2, 4];
            let mut output = [0; 6];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn second_longer() {
            let mut first = [2, 4];
            let mut second = [0, 1, 3, 5];
            let mut output = [0; 6];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn first_greater() {
            let mut first = [1];
            let mut second = [0];
            let mut output = [0; 2];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1]);
        }

        #[test]
        fn second_greater() {
            let mut first = [0];
            let mut second = [1];
            let mut output = [0; 2];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1]);
        }

        #[test]
        fn back_and_forth() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [0; 6];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        #[should_panic(expected = "output length must be sum of input lengths")]
        fn output_cannot_be_smaller() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [];

            parallel(&mut first, &mut second, &mut output);
        }

        #[test]
        #[should_panic(expected = "output length must be sum of input lengths")]
        fn output_cannot_be_larger() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [0; 256];

            parallel(&mut first, &mut second, &mut output);
        }
    }

    mod in_place {
        use super::*;

        #[test]
        fn first_empty() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            in_place(&mut elements, 0);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn second_empty() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            in_place(&mut elements, 6);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn both_empty() {
            let mut elements = [0; 0];

            in_place(&mut elements, 0);

            assert_eq!(elements, []);
        }

        #[test]
        fn first_longer() {
            let mut elements = [0, 1, 3, 5, 2, 4];

            in_place(&mut elements, 4);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn second_longer() {
            let mut elements = [2, 4, 0, 1, 3, 5];

            in_place(&mut elements, 2);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn first_greater() {
            let mut elements = [1, 0];

            in_place(&mut elements, 1);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn second_greater() {
            let mut elements = [0, 1];

            in_place(&mut elements, 1);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn back_and_forth() {
            let mut elements = [0, 2, 4, 1, 3, 5];

            in_place(&mut elements, 3);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }
    }
}
