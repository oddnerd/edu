//! Implementations of [Merge](https://en.wikipedia.org/wiki/Merge_algorithm).

/// Merge the `first` and `second` slice into the `output` slice.
///
/// <div class="warning">
/// If either input is not sorted increasingly, the result is meaningless.
/// </div>
///
/// # Panics
/// If the length of `output` is not exactly the sum of input lengths.
///
/// # Methodology
/// Each input is independently iterated. While there is still an un-merged
/// element from both, they are compared and the smaller value is pushed to the
/// output. If/when only one of the inputs has un-merged elements, all those
/// elements are pushed in order to the output.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(N) | O(N) | O(N) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | O(1) | O(1) |
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
pub fn iterative<T: Ord>(first: &mut [T], second: &mut [T], output: &mut [T]) {
    debug_assert!(
        first.is_sorted() && second.is_sorted(),
        "elements must be sorted in increasing order"
    );

    assert_eq!(
        Some(output.len()),
        usize::checked_add(first.len(), second.len()),
        "output length must be sum of input lengths"
    );

    let mut first = first.iter_mut().peekable();
    let mut second = second.iter_mut().peekable();

    #[expect(clippy::shadow_unrelated, reason = "element from the slice")]
    for output in output {
        match (first.peek_mut(), second.peek_mut()) {
            (Some(left), Some(right)) => {
                if left <= right {
                    core::mem::swap(output, *left);
                    _ = first.next();
                } else {
                    core::mem::swap(output, *right);
                    _ = second.next();
                }
            }
            (Some(left), None) => {
                core::mem::swap(output, *left);
                _ = first.next();
            }
            (None, Some(right)) => {
                core::mem::swap(output, *right);
                _ = second.next();
            }
            (None, None) => unreachable!("more output elements than input"),
        };
    }
}

/// Merge the `first` and `second` slice into the `output` slice.
///
/// This algorithm is _NOT_ stable meaning the order of equal elements
/// is _NOT_ guaranteed.
///
/// For the convenience of implementation to not depend on a particular
/// executor, this method executes synchronously within the single calling
/// thread. However, the implementation is of a parallel algorithm that could
/// be trivially modified to execute asynchronously.
///
/// # Panics
/// This method has the precondition that `output` has the _exact_ same length
/// as the sum of the input lengths.
///
/// # Performance
/// This method takes O(N * log N) time and consumes O(log N) memory.
///
/// If ran asynchronously, this method takes O(log<sup>2</sup> N) time instead.
///
/// # Examples
/// ```
/// use rust::algorithm::merge::parallel;
///
/// let mut first  = [0, 2, 4];
/// let mut second = [1, 3, 5];
/// let mut output = [0; 6];
///
/// parallel(&mut first, &mut second, &mut output);
///
/// assert_eq!(output, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn parallel<T: Ord>(first: &mut [T], second: &mut [T], output: &mut [T]) {
    let Some(elements) = usize::checked_add(first.len(), second.len()) else {
        panic!("output must be larger than usize::MAX which is impossible");
    };

    assert_eq!(
        output.len(),
        elements,
        "output length must be sum of input lengths"
    );

    if first.len() < second.len() {
        return parallel(second, first, output);
    }

    let middle = first.len() / 2;

    let Some(middle_element) = first.get(middle) else {
        debug_assert!(first.is_empty(), "only condition it is none");

        return;
    };

    // Find the position in `second` where the middle element would go.
    // This means `second[intersect..] > first[middle..]`. for every element.
    // Note that binary search is O(log N) significantly contributing to time.
    let intersect = match second.binary_search(middle_element) {
        // If `Ok`, then an equivalent element was found. However, if `Err`,
        // then the index is where a matching element could be inserted while
        // maintaining sorted order, so either way the index we want.
        Err(index) | Ok(index) => index,
    };

    let (first_left, first_right) = first.split_at_mut(middle);
    let (second_left, second_right) = second.split_at_mut(intersect);

    let Some(partition_point) = usize::checked_add(middle, intersect) else {
        unreachable!("`output.len() < usize::MAX` therefore this is too");
    };

    let (output_left, output_right) = output.split_at_mut(partition_point);

    // Alongside partitioning the slices, this also determines the specific
    // sorted position for that middle element since we know how many elements
    // are less than it, so place it in the output and discard it from inputs.
    let Some((sorted_position, output_right)) = output_right.split_first_mut() else {
        unreachable!("binary search yields and index within bounds");
    };

    let Some((sorted_element, first_right)) = first_right.split_first_mut() else {
        unreachable!("contains at least the middle element");
    };

    core::mem::swap(sorted_position, sorted_element);

    // The following calls could be executed concurrently.
    parallel(first_left, second_left, output_left);
    parallel(first_right, second_right, output_right);
}

/// Merge independently sorted `[..middle]` and `[middle..]` together in-place.
///
/// # Panics
/// This panics if the provided `middle` is out of bounds.
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
pub fn in_place<T: Ord>(elements: &mut [T], middle: usize) {
    let mut left = 0..middle;
    let mut right = middle..elements.len();

    while !left.is_empty() && !right.is_empty() {
        if elements.get(left.start) <= elements.get(right.start) {
            // Already in sorted position, advance to next element.
            _ = left.next();
        } else {
            let Some(rest_of_left_and_first_of_right) = elements.get_mut(left.start..=right.start)
            else {
                unreachable!("provided `middle` is in bounds, this is too");
            };

            // This places the first element of the right in front of the rest
            // of the left since it must be less than them. Note that this
            // is O(N) significantly contributing to time.
            rest_of_left_and_first_of_right.rotate_right(1);
            _ = right.next();

            let (Some(updated_left_start), Some(updated_left_end)) =
                (left.start.checked_add(1), left.end.checked_add(1))
            else {
                debug_assert!(
                    left.start == usize::MAX || left.end == usize::MAX,
                    "only condition this branch is invoked"
                );

                // This implies the remaining left elements are sorted order.
                return;
            };

            left = updated_left_start..updated_left_end;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    mod iterative {
        use super::*;

        #[test]
        fn first_empty() {
            let mut first = [];
            let mut second = [0, 1, 2, 3, 4, 5];
            let mut output = [usize::default(); 6];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn second_empty() {
            let mut first = [0, 1, 2, 3, 4, 5];
            let mut second = [];
            let mut output = [usize::default(); 6];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn both_empty() {
            let mut first = [];
            let mut second = [];
            let mut output: [usize; 0] = [];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, []);
        }

        #[test]
        fn first_longer() {
            let mut first = [0, 1, 3, 5];
            let mut second = [2, 4];
            let mut output = [usize::default(); 6];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn second_longer() {
            let mut first = [2, 4];
            let mut second = [0, 1, 3, 5];
            let mut output = [usize::default(); 6];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn first_greater() {
            let mut first = [1];
            let mut second = [0];
            let mut output = [usize::default(); 2];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1]);
        }

        #[test]
        fn second_greater() {
            let mut first = [0];
            let mut second = [1];
            let mut output = [usize::default(); 2];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1]);
        }

        #[test]
        fn back_and_forth() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [usize::default(); 6];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        #[should_panic = "output length must be sum of input lengths"]
        fn output_cannot_be_smaller() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [];

            iterative(&mut first, &mut second, &mut output);
        }

        #[test]
        #[should_panic = "output length must be sum of input lengths"]
        fn output_cannot_be_larger() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [usize::default(); 256];

            iterative(&mut first, &mut second, &mut output);
        }
    }

    mod parallel {
        use super::*;

        #[test]
        fn first_empty() {
            let mut first = [];
            let mut second = [0, 1, 2, 3, 4, 5];
            let mut output = [usize::default(); 6];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn second_empty() {
            let mut first = [0, 1, 2, 3, 4, 5];
            let mut second = [];
            let mut output = [usize::default(); 6];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn both_empty() {
            let mut first = [];
            let mut second = [];
            let mut output: [usize; 0] = [];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, []);
        }

        #[test]
        fn first_longer() {
            let mut first = [0, 1, 3, 5];
            let mut second = [2, 4];
            let mut output = [usize::default(); 6];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn second_longer() {
            let mut first = [2, 4];
            let mut second = [0, 1, 3, 5];
            let mut output = [usize::default(); 6];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn first_greater() {
            let mut first = [1];
            let mut second = [0];
            let mut output = [usize::default(); 2];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1]);
        }

        #[test]
        fn second_greater() {
            let mut first = [0];
            let mut second = [1];
            let mut output = [usize::default(); 2];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1]);
        }

        #[test]
        fn back_and_forth() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [usize::default(); 6];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        #[should_panic = "output length must be sum of input lengths"]
        fn output_cannot_be_smaller() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [];

            parallel(&mut first, &mut second, &mut output);
        }

        #[test]
        #[should_panic = "output length must be sum of input lengths"]
        fn output_cannot_be_larger() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [usize::default(); 256];

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
            let mut elements: [usize; 0] = [];

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
