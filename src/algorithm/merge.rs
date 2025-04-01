//! Implementations of [Merge](https://en.wikipedia.org/wiki/Merge_algorithm).

/// Merge the `first` and `second` input into the `output` slice.
///
/// <div class="warning">
/// If either input is not sorted increasingly, the result is unspecified.
/// </div>
///
/// # Panics
/// If the length of `output` is not exactly the sum of input lengths.
///
/// # Algorithm
/// Each input is independently iterated. While there is still an un-merged
/// element from both, they are compared and the smaller value is pushed to the
/// output. If/when only one of the inputs has un-merged elements, all those
/// elements are pushed in order to the output.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(N) | 𝛀(N) | 𝚯(N) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
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

/// Merge the `first` and `second` input into the `output` slice.
///
/// <div class="warning">
/// If either input is not sorted increasingly, the result is unspecified.
/// </div>
///
/// <div class="warning">
/// This is unstable so the order of equivalent elements is not guaranteed.
/// </div>
///
/// # Panics
/// If the length of `output` is not exactly the sum of input lengths.
///
/// # Algorithm
/// Find the index within the second input such that it would maintain sorted
/// order if the middle element of the first input was inserted there. Notice
/// that all elements of second input before that index occur before the middle
/// element of the first input, and the sum of elements before the middle of
/// the first input and the found index of the second input is the sorted
/// position of that middle element. The first input can be split at that
/// middle element, and the second input can be split at that found index. The
/// left halves can then be merged asynchronously of merging the right halves.
///
/// # Performance
/// #### Executed Synchronously
/// ##### Time Complexity
/// | Worst | Best | Average |
/// | :-: |  :-: | :-: |
/// | O(N ⋅ log N) | 𝛀(N ⋅ log N)| 𝚯(N ⋅ log N) |
///
/// ##### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(N) | 𝛀(N) | 𝚯(N) |
///
/// #### Executed Asynchronously
/// ##### Time Complexity
/// | Worst | Best | Average |
/// | :-: |  :-: | :-: |
/// | O(log<sup>2</sup> N) | 𝛀(log<sup>2</sup> N) | 𝚯(log<sup>2</sup> N) |
///
/// ##### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(log N) | 𝛀(log N) | 𝚯(log N) |
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
    debug_assert!(
        first.is_sorted() && second.is_sorted(),
        "elements must be sorted in increasing order"
    );

    assert_eq!(
        Some(output.len()),
        usize::checked_add(first.len(), second.len()),
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
        // maintaining sorted order, so either way the desired index.
        Err(index) | Ok(index) => index,
    };

    let (first_left, first_right) = first.split_at_mut(middle);
    let (second_left, second_right) = second.split_at_mut(intersect);

    let Some(partition_point) = usize::checked_add(middle, intersect) else {
        unreachable!("output can contain all elements from both inputs");
    };

    let (output_left, output_right) = output.split_at_mut(partition_point);

    // Alongside partitioning the slices, this also determines the specific
    // sorted position for that middle element since we know how many elements
    // are less than it, so place it in the output and discard it from inputs.
    let Some((sorted_position, output_right)) = output_right.split_first_mut() else {
        unreachable!("binary search yields an index within bounds");
    };

    let Some((sorted_element, first_right)) = first_right.split_first_mut() else {
        unreachable!("contains at least the middle element");
    };

    core::mem::swap(sorted_position, sorted_element);

    // The following calls could be executed in parallel.
    parallel(first_left, second_left, output_left);
    parallel(first_right, second_right, output_right);
}

/// Merge independently sorted `[..middle]` and `[middle..]` together in-place.
///
/// <div class="warning">
/// If either input is not sorted increasingly, the result is unspecified.
/// </div>
///
/// # Panics
/// If the provided `middle` is out of bounds.
///
/// # Algorithm
/// If the next element from the left input is the smallest, then it is already
/// in sorted position so the left can be advanced. However, if the next
/// element from the right input is smaller, then all remaining elements from
/// the left input plus the next right element can be rotated right once (with
/// wrapping behaviour) thereby placing that right element into sorted position
/// ahead of both inputs so the right input can then be advanced the algorithm
/// repeated until either input is exhausted, in which case the remaining
/// elements are therefore in sorted position to the right of everything else.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(N<sup>2</sup>) | 𝛀(N) | 𝚯(N<sup>2</sup>) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
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
    // TODO: determine average time complexity.

    assert!(middle <= elements.len(), "middle must be in bounds");

    let mut left = 0..middle;
    let mut right = middle..elements.len();

    debug_assert!(
        elements.get(left.clone()).is_some_and(<[T]>::is_sorted)
            && elements.get(right.clone()).is_some_and(<[T]>::is_sorted),
        "elements must be sorted in increasing order"
    );

    while !left.is_empty() && !right.is_empty() {
        if elements.get(left.start) <= elements.get(right.start) {
            // Already in sorted position, advance to next element.
            _ = left.next();
        } else {
            let Some(unsorted) = elements.get_mut(left.start..=right.start) else {
                unreachable!("inside loop => ranges are in bounds");
            };

            // This places the first element of the right in front of the rest
            // of the left since it must be less than them. Note that this
            // is O(N) significantly contributing to time.
            unsorted.rotate_right(1);
            _ = right.next();

            let (Some(start), Some(end)) = (left.start.checked_add(1), left.end.checked_add(1))
            else {
                debug_assert!(
                    left.start == usize::MAX || left.end == usize::MAX,
                    "only condition this branch is invoked"
                );

                // This implies the remaining left elements are sorted order.
                return;
            };

            left = start..end;
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    mod iterative {
        use super::*;

        #[test]
        #[should_panic = "output length must be sum of input lengths"]
        fn when_length_of_output_is_smaller_than_sum_of_input_lengths_then_panics() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [];

            debug_assert!(output.len() < first.len() + second.len());

            iterative(&mut first, &mut second, &mut output);
        }

        #[test]
        #[should_panic = "output length must be sum of input lengths"]
        fn when_length_of_output_is_larger_than_sum_of_input_lengths_then_panics() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [usize::default(); 7];

            debug_assert!(output.len() > first.len() + second.len());

            iterative(&mut first, &mut second, &mut output);
        }

        #[test]
        #[cfg_attr(not(debug_assertions), ignore)]
        #[should_panic = "elements must be sorted in increasing order"]
        fn when_first_input_is_not_sorted_increasingly_then_panics() {
            let mut first = [4, 2, 0];
            let mut second = [1, 3, 5];
            let mut output = [usize::default(); 6];

            debug_assert!(!first.is_sorted());
            debug_assert!(second.is_sorted());

            iterative(&mut first, &mut second, &mut output);
        }

        #[test]
        #[cfg_attr(not(debug_assertions), ignore)]
        #[should_panic = "elements must be sorted in increasing order"]
        fn when_second_input_is_not_sorted_increasingly_then_panics() {
            let mut first = [0, 2, 4];
            let mut second = [5, 3, 1];
            let mut output = [usize::default(); 6];

            debug_assert!(first.is_sorted());
            debug_assert!(!second.is_sorted());

            iterative(&mut first, &mut second, &mut output);
        }

        #[test]
        #[cfg_attr(not(debug_assertions), ignore)]
        #[should_panic = "elements must be sorted in increasing order"]
        fn when_both_inputs_are_not_sorted_increasingly_then_panics() {
            let mut first = [4, 2, 0];
            let mut second = [5, 3, 1];
            let mut output = [usize::default(); 6];

            debug_assert!(!first.is_sorted());
            debug_assert!(!second.is_sorted());

            iterative(&mut first, &mut second, &mut output);
        }

        #[test]
        fn when_first_input_is_empty_then_output_is_elements_of_second_input() {
            let mut first = [];
            let mut second = [0, 1, 2, 3, 4, 5];
            let mut output = [usize::default(); 6];

            debug_assert!(first.is_empty());
            debug_assert!(!second.is_empty());

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_second_input_is_empty_then_output_is_elements_of_first_input() {
            let mut first = [0, 1, 2, 3, 4, 5];
            let mut second = [];
            let mut output = [usize::default(); 6];

            debug_assert!(!first.is_empty());
            debug_assert!(second.is_empty());

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_both_inputs_are_empty_then_output_is_empty() {
            let mut first = [];
            let mut second = [];
            let mut output: [usize; 0] = [];

            debug_assert!(first.is_empty());
            debug_assert!(second.is_empty());

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, []);
        }

        #[test]
        fn when_elements_from_first_input_are_less_than_elements_from_second_input_then_output_has_first_elements_before_second()
         {
            let mut first = [0, 1, 2];
            let mut second = [3, 4, 5];
            let mut output = [usize::default(); 6];

            debug_assert!(
                first
                    .iter()
                    .all(|first| second.iter().all(|second| first < second))
            );

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_elements_from_second_input_are_less_than_elements_from_first_input_then_output_has_second_elements_before_first()
         {
            let mut first = [3, 4, 5];
            let mut second = [0, 1, 2];
            let mut output = [usize::default(); 6];

            debug_assert!(
                second
                    .iter()
                    .all(|second| first.iter().all(|first| second < first))
            );

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_the_smallest_element_alternates_between_the_first_and_second_input_then_output_is_sorted_increasingly()
         {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [usize::default(); 6];

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_first_input_is_longer_than_second_then_remaining_are_appended_to_output() {
            let mut first = [2, 3, 4, 5];
            let mut second = [0, 1];
            let mut output = [usize::default(); 6];

            debug_assert!(first.len() > second.len());

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_second_input_is_longer_than_first_then_remaining_are_appended_to_output() {
            let mut first = [0, 1];
            let mut second = [2, 3, 4, 5];
            let mut output = [usize::default(); 6];

            debug_assert!(second.len() > first.len());

            iterative(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }
    }

    mod parallel {
        use super::*;

        #[test]
        #[should_panic = "output length must be sum of input lengths"]
        fn when_length_of_output_is_smaller_than_sum_of_input_lengths_then_panics() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [];

            debug_assert!(output.len() < first.len() + second.len());

            parallel(&mut first, &mut second, &mut output);
        }

        #[test]
        #[should_panic = "output length must be sum of input lengths"]
        fn when_length_of_output_is_larger_than_sum_of_input_lengths_then_panics() {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [usize::default(); 7];

            debug_assert!(output.len() > first.len() + second.len());

            parallel(&mut first, &mut second, &mut output);
        }

        #[test]
        #[cfg_attr(not(debug_assertions), ignore)]
        #[should_panic = "elements must be sorted in increasing order"]
        fn when_first_input_is_not_sorted_increasingly_then_panics() {
            let mut first = [4, 2, 0];
            let mut second = [1, 3, 5];
            let mut output = [usize::default(); 6];

            debug_assert!(!first.is_sorted());
            debug_assert!(second.is_sorted());

            parallel(&mut first, &mut second, &mut output);
        }

        #[test]
        #[cfg_attr(not(debug_assertions), ignore)]
        #[should_panic = "elements must be sorted in increasing order"]
        fn when_second_input_is_not_sorted_increasingly_then_panics() {
            let mut first = [0, 2, 4];
            let mut second = [5, 3, 1];
            let mut output = [usize::default(); 6];

            debug_assert!(first.is_sorted());
            debug_assert!(!second.is_sorted());

            parallel(&mut first, &mut second, &mut output);
        }

        #[test]
        #[cfg_attr(not(debug_assertions), ignore)]
        #[should_panic = "elements must be sorted in increasing order"]
        fn when_both_inputs_are_not_sorted_increasingly_then_panics() {
            let mut first = [4, 2, 0];
            let mut second = [5, 3, 1];
            let mut output = [usize::default(); 6];

            debug_assert!(!first.is_sorted());
            debug_assert!(!second.is_sorted());

            parallel(&mut first, &mut second, &mut output);
        }

        #[test]
        fn when_first_input_is_empty_then_output_is_elements_of_second_input() {
            let mut first = [];
            let mut second = [0, 1, 2, 3, 4, 5];
            let mut output = [usize::default(); 6];

            debug_assert!(first.is_empty());
            debug_assert!(!second.is_empty());

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_second_input_is_empty_then_output_is_elements_of_first_input() {
            let mut first = [0, 1, 2, 3, 4, 5];
            let mut second = [];
            let mut output = [usize::default(); 6];

            debug_assert!(!first.is_empty());
            debug_assert!(second.is_empty());

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_both_inputs_are_empty_then_output_is_empty() {
            let mut first = [];
            let mut second = [];
            let mut output: [usize; 0] = [];

            debug_assert!(first.is_empty());
            debug_assert!(second.is_empty());

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, []);
        }

        #[test]
        fn when_elements_from_first_input_are_less_than_elements_from_second_input_then_output_has_first_elements_before_second()
         {
            let mut first = [0, 1, 2];
            let mut second = [3, 4, 5];
            let mut output = [usize::default(); 6];

            debug_assert!(
                first
                    .iter()
                    .all(|first| second.iter().all(|second| first < second))
            );

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_elements_from_second_input_are_less_than_elements_from_first_input_then_output_has_second_elements_before_first()
         {
            let mut first = [3, 4, 5];
            let mut second = [0, 1, 2];
            let mut output = [usize::default(); 6];

            debug_assert!(
                second
                    .iter()
                    .all(|second| first.iter().all(|first| second < first))
            );

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_the_smallest_element_alternates_between_the_first_and_second_input_then_output_is_sorted_increasingly()
         {
            let mut first = [0, 2, 4];
            let mut second = [1, 3, 5];
            let mut output = [usize::default(); 6];

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_first_input_is_longer_than_second_then_remaining_are_appended_to_output() {
            let mut first = [2, 3, 4, 5];
            let mut second = [0, 1];
            let mut output = [usize::default(); 6];

            debug_assert!(first.len() > second.len());

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_second_input_is_longer_than_first_then_remaining_are_appended_to_output() {
            let mut first = [0, 1];
            let mut second = [2, 3, 4, 5];
            let mut output = [usize::default(); 6];

            debug_assert!(second.len() > first.len());

            parallel(&mut first, &mut second, &mut output);

            assert_eq!(output, [0, 1, 2, 3, 4, 5]);
        }
    }

    mod in_place {
        use super::*;

        #[test]
        #[should_panic = "middle must be in bounds"]
        fn when_middle_is_outside_then_bounds_of_elements_then_panics() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            let middle = 7;

            debug_assert!(middle > elements.len());

            in_place(&mut elements, middle);
        }

        #[test]
        #[cfg_attr(not(debug_assertions), ignore)]
        #[should_panic = "elements must be sorted in increasing order"]
        fn when_first_input_is_not_sorted_increasingly_then_panics() {
            let mut elements = [4, 2, 0, 1, 3, 5];
            let middle = 3;

            debug_assert!(!elements[..middle].is_sorted());
            debug_assert!(elements[middle..].is_sorted());

            in_place(&mut elements, middle);
        }

        #[test]
        #[cfg_attr(not(debug_assertions), ignore)]
        #[should_panic = "elements must be sorted in increasing order"]
        fn when_second_input_is_not_sorted_increasingly_then_panics() {
            let mut elements = [0, 2, 4, 5, 3, 1];
            let middle = 3;

            debug_assert!(elements[..middle].is_sorted());
            debug_assert!(!elements[middle..].is_sorted());

            in_place(&mut elements, middle);
        }

        #[test]
        #[cfg_attr(not(debug_assertions), ignore)]
        #[should_panic = "elements must be sorted in increasing order"]
        fn when_both_inputs_are_not_sorted_increasingly_then_panics() {
            let mut elements = [4, 2, 0, 5, 3, 1];
            let middle = 3;

            debug_assert!(!elements[..middle].is_sorted());
            debug_assert!(!elements[middle..].is_sorted());

            in_place(&mut elements, middle);
        }

        #[test]
        fn when_first_input_is_empty_then_output_is_elements_of_second_input() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            let middle = 0;

            debug_assert!(elements[..middle].is_empty());
            debug_assert!(!elements[middle..].is_empty());

            in_place(&mut elements, middle);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_second_input_is_empty_then_output_is_elements_of_first_input() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            let middle = elements.len();

            debug_assert!(!elements[..middle].is_empty());
            debug_assert!(elements[middle..].is_empty());

            in_place(&mut elements, middle);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_both_inputs_are_empty_then_output_is_empty() {
            let mut elements: [usize; 0] = [];
            let middle = 0;

            debug_assert!(elements[..middle].is_empty());
            debug_assert!(elements[middle..].is_empty());

            in_place(&mut elements, middle);

            assert_eq!(elements, []);
        }

        #[test]
        fn when_elements_from_first_input_are_less_than_elements_from_second_input_then_output_has_first_elements_before_second()
         {
            let mut elements = [0, 1, 2, 3, 4, 5];
            let middle = 3;

            let (first, second) = elements.split_at(middle);
            debug_assert!(
                first
                    .iter()
                    .all(|first| second.iter().all(|second| first < second))
            );

            in_place(&mut elements, middle);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_elements_from_second_input_are_less_than_elements_from_first_input_then_output_has_second_elements_before_first()
         {
            let mut elements = [3, 4, 5, 0, 1, 2];
            let middle = 3;

            let (first, second) = elements.split_at(middle);
            debug_assert!(
                second
                    .iter()
                    .all(|second| first.iter().all(|first| second < first))
            );

            in_place(&mut elements, middle);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_the_smallest_element_alternates_between_the_first_and_second_input_then_output_is_sorted_increasingly()
         {
            let mut elements = [0, 2, 4, 1, 3, 5];
            let middle = 3;

            in_place(&mut elements, middle);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_first_input_is_longer_than_second_then_remaining_are_appended_to_output() {
            let mut elements = [2, 3, 4, 5, 0, 1];
            let middle = 4;

            debug_assert!(elements[..middle].len() > elements[middle..].len());

            in_place(&mut elements, middle);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn when_second_input_is_longer_than_first_then_remaining_are_appended_to_output() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            let middle = 2;

            debug_assert!(elements[middle..].len() > elements[..middle].len());

            in_place(&mut elements, middle);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }
    }
}
