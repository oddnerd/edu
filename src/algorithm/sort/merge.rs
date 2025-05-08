//! Implementations of [Merge Sort](https://en.wikipedia.org/wiki/Merge_sort).

use super::super::merge;

/// Sort `elements` via top-down merge sort.
///
/// <div class="warning">
/// If `auxiliary` is not a clone of `elements`, the result is unspecified.
/// </div>
///
/// # Algorithm
/// Recursively divide `elements` into two halves until each contains only
/// a single element and is therefore in sorted order. Then merge both
/// independently sorted halves together thereby sorting them into one
/// larger sorted section which can be passed up the call stack to be merged
/// with another.
///
/// # Performance
/// This algorithm consumes O(log N) memory and has O(N ⋅ log N) time
/// complexity regardless of input.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::merge::top_down;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
/// let mut auxiliary = elements.clone();
///
/// top_down(&mut elements, &mut auxiliary);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn top_down<T: Ord>(elements: &mut [T], auxiliary: &mut [T]) {
    debug_assert!(elements == auxiliary, "auxiliary must be clone of elements");

    if elements.len() <= 1 {
        return;
    }

    let (left_input, right_input) = elements.split_at_mut(elements.len() / 2);
    let (left_auxiliary, right_auxiliary) = auxiliary.split_at_mut(auxiliary.len() / 2);

    // Alternating input/auxiliary ensures top-level caller merges into output.
    top_down(left_auxiliary, left_input);
    top_down(right_auxiliary, right_input);

    merge::iterative(left_auxiliary, right_auxiliary, elements);
}

/// Sort `elements` via natural merge sort.
///
/// <div class="warning">
/// If `auxiliary` is not a clone of `elements`, the result is unspecified.
/// </div>
///
/// # Algorithm
/// Unlike traditional [`top_down`] merge sort, this algorithm takes advantage
/// of natural runs of sorted elements. In effect, this variation first splits
/// `elements` into naturally sorted sub-slices and then merges them thereby
/// splitting the original input optimally to prevent unnecessary recursion.
///
/// # Performance
/// This algorithm consumes O(N) memory and has O(N ⋅ log N) time complexity in
/// the worst-cast when the input is in reverse sorted order, consumes 𝛀(1)
/// memory and has 𝛀(N) time complexity in the best-case when the input is
/// already sorted, and on average consumes 𝚯(N) memory with 𝚯(N ⋅ log N) time
/// complexity.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::merge::natural;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
/// let mut auxiliary = elements.clone();
///
/// natural(&mut elements, &mut auxiliary);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn natural<T: Ord>(elements: &mut [T], auxiliary: &mut [T]) {
    debug_assert!(elements == auxiliary, "auxiliary must be clone of elements");

    if elements.len() <= 1 {
        return;
    }

    // Determine the number of front elements in sorted order.
    let mut length: usize = 1;

    for pair in elements.windows(2) {
        if pair.first() > pair.last() {
            break;
        }

        if let Some(incremented) = length.checked_add(1) {
            length = incremented;
        } else {
            unreachable!("slice cannot be longer than `usize::MAX`");
        }
    }

    // Split that run of naturally sorted elements and sort the rest.
    let (_sorted_input, unsorted_input) = elements.split_at_mut(length);
    let (sorted_auxiliary, unsorted_auxiliary) = auxiliary.split_at_mut(length);

    // Alternating input/auxiliary ensures top-level caller merges into output.
    natural(unsorted_auxiliary, unsorted_input);

    merge::iterative(sorted_auxiliary, unsorted_auxiliary, elements);
}

/// Sort `elements` via bottom-up merge sort.
///
/// <div class="warning">
/// If `auxiliary` is not a clone of `elements`, the result is unspecified.
/// </div>
///
/// # Algorithm
/// In contrast to [`top_down`] which recurses down to sub-slices of a single
/// element, this implementation iterates over a length starting at one element
/// and dividing the input into chunks of that length which can then be merged
/// to create a sorted sub-slice of double length effectively ascending the
/// recursive stack without needing to first descend down.
///
/// # Performance
/// This algorithm consumes O(1) memory and has O(N ⋅ log N) time
/// complexity regardless of input.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::merge::bottom_up;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
/// let mut auxiliary = elements.clone();
///
/// bottom_up(&mut elements, &mut auxiliary);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn bottom_up<T: Ord>(elements: &mut [T], auxiliary: &mut [T]) {
    debug_assert!(elements == auxiliary, "auxiliary must be clone of elements");

    let Some(bound) = elements.len().checked_ilog2() else {
        debug_assert!(elements.is_empty(), "only condition ilog2 is none");

        return;
    };

    let Some(bound) = bound.checked_add(1) else {
        unreachable!("bound is at most the number of bits in usize");
    };

    for length in (1..=bound).map_while(|exponent| usize::checked_pow(2, exponent)) {
        let elements = elements.chunks_mut(length);
        let auxiliary = auxiliary.chunks_mut(length);

        for (input, output) in elements.zip(auxiliary) {
            let Some((left, right)) = input.split_at_mut_checked(length / 2) else {
                debug_assert!(input.len() < length, "chunk is final elements not evenly divided");
                debug_assert!(input.is_sorted(), "this implies it is already sorted and can be merged in next iteration");

                continue;
            };

            merge::iterative(left, right, output);

            input.swap_with_slice(output);
        }
    }
}

/// Sort `elements` via in-place merge sort.
///
/// <div class="warning">
/// This is unstable so the order of equivalent elements is not guaranteed.
/// </div>
///
/// # Algorithm
/// Sort the left half of the slice into the right half so the right half is
/// sorted and the left half is unsorted. Thenceforth sort the right half of
/// the unsorted fraction into the left half, merge the sorted fraction into
/// the original sorted right half thereby combining the sorted elements on the
/// right and unsorted on the left, repeating until all elements are sorted.
///
/// # Performance
/// This algorithm consumes O(1) memory and has O(N ⋅ log N) time
/// complexity regardless of input.
///
/// # Citation
/// This algorithm is from the following citation:
///
/// ```bibtex
/// @article{10.5555/642136.642138,
///     author     = {Jyrki Katajainen and Tomi Pasanen and Jukka Teuhola},
///     title      = {Practical in-place mergesort},
///     journal    = {Nordic Journal of Computing},
///     issue_date = {Spring 1996},
///     publisher  = {Publishing Association Nordic Journal of Computing},
///     volume     = {3},
///     number     = {1},
///     pages      = {27–40},
///     issn       = {1236-6064},
///     date       = {1996-03-01},
/// }
/// ```
///
/// # Examples
/// ```
/// use rust::algorithm::sort::merge::in_place;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// in_place(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn in_place<T: Ord>(elements: &mut [T]) {
    /// Merge two sub-slices into a potentially overlapping sub-slice.
    fn merge<T: Ord>(
        elements: &mut [T],
        first: core::ops::Range<usize>,
        second: core::ops::Range<usize>,
        output: usize,
    ) {
        let mut first = first.peekable();
        let mut second = second.peekable();

        for output_index in output..elements.len() {
            let input_index = match (first.peek(), second.peek()) {
                (Some(first_index), Some(second_index)) => {
                    if elements.get(*first_index) < elements.get(*second_index) {
                        first.next()
                    } else {
                        second.next()
                    }
                }
                (Some(_), None) => first.next(),
                (None, Some(_)) => second.next(),
                (None, None) => return,
            };

            let Some(input_index) = input_index else {
                unreachable!("caller provided invalid ranges");
            };

            elements.swap(output_index, input_index);
        }
    }

    /// Sort a `range` of `elements` into the same slice, starting at `output`.
    fn sort_into<T: Ord>(elements: &mut [T], range: core::ops::Range<usize>, output: usize) {
        if range.len() > 1 {
            let middle = range.len().div_euclid(2);

            let Some(sorting) = elements.get_mut(range.clone()) else {
                unreachable!("caller ensures range is within bounds");
            };

            let (left, right) = sorting.split_at_mut(middle);

            in_place(left);
            in_place(right);

            let Some(middle) = range.start.checked_add(middle) else {
                unreachable!("less than `range.end` => less than `usize::MAX`");
            };

            merge(elements, range.start..middle, middle..range.end, output);
        } else {
            elements.swap(output, range.start);
        }
    }

    if elements.len() <= 1 {
        return;
    }

    // Sort left half `..middle` into right half `middle..`.
    let middle = elements.len().div_euclid(2);
    let mut output = elements.len().div_ceil(2);
    sort_into(elements, 0..middle, output);

    // Sort the right half of the unsorted section into the left half then
    // merge with the already sorted section via swapping with the unsorted.
    while output > 2 {
        // Unsorted: [..split]
        // Sorted: [split..]
        let split = output;

        // Unsorted: [..output]
        // To be sorted [output..split]
        // Already sorted: [split..]
        output = split.div_ceil(2);

        // Sort [output..split] into [..output]
        sort_into(elements, output..split, 0);

        // Unsorted: [..output]
        // Sorted: [output..]
        merge(
            elements,
            0..split.div_euclid(2),
            split..elements.len(),
            output,
        );
    }

    // Sort the remaining elements in [..output] via insertion sort.
    for remaining in (0..output).rev() {
        let Some(final_index) = elements.len().checked_sub(1) else {
            unreachable!("there is at least one element");
        };

        for current in remaining..final_index {
            let Some(next) = current.checked_add(1) else {
                unreachable!("`current` is at most `usize::MAX - 1`");
            };

            if elements.get(current) > elements.get(next) {
                elements.swap(current, next);
            } else {
                break;
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    mod top_down {
        use super::*;

        #[test]
        #[cfg_attr(not(debug_assertions), ignore)]
        #[should_panic = "auxiliary must be clone of elements"]
        fn when_auxiliary_is_not_a_clone_of_elements_then_panics() {
            let mut elements = [5, 4, 3, 2, 1];
            let mut auxiliary = [0, 0, 0, 0, 0];

            top_down(&mut elements, &mut auxiliary);
        }

        #[test]
        fn when_empty_then_does_nothing() {
            let mut elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            let mut auxiliary = elements;

            top_down(&mut elements, &mut auxiliary);

            assert_eq!(elements, []);
        }

        #[test]
        fn when_single_element_then_does_not_modify_it() {
            for element in 0..256 {
                let mut elements = [element];

                debug_assert_eq!(elements.len(), 1);

                let mut auxiliary = elements;

                top_down(&mut elements, &mut auxiliary);

                assert_eq!(elements, [element]);
            }
        }

        #[test]
        fn when_all_elements_are_equivalent_then_does_not_modify_them() {
            for value in 0..256 {
                for length in 2..256 {
                    let mut elements: Vec<_> = core::iter::repeat_n(value, length).collect();

                    debug_assert!(elements.iter().all(|element| element == &value));

                    let mut auxiliary = elements.clone();

                    top_down(&mut elements, &mut auxiliary);

                    assert!(elements.into_iter().all(|element| element == value));
                }
            }
        }

        #[test]
        fn when_already_sorted_then_maintains_order() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).collect();

                debug_assert!(elements.is_sorted());

                let mut auxiliary = elements.clone();

                top_down(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_in_reverse_sorted_order_then_is_reversed() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.iter().rev().is_sorted());

                let mut auxiliary = elements.clone();

                top_down(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_elements_are_repeated_then_they_are_grouped_together() {
            for repeat in 2..128 {
                let mut elements: Vec<_> = (0..256)
                    .map(|element| {
                        if element % repeat == 0 {
                            repeat
                        } else {
                            element
                        }
                    })
                    .collect();

                let count = elements.len().div_ceil(repeat);

                debug_assert_eq!(
                    elements
                        .iter()
                        .filter(|element| *element == &repeat)
                        .count(),
                    count
                );

                let mut auxiliary = elements.clone();

                top_down(&mut elements, &mut auxiliary);

                let index = elements
                    .iter()
                    .position(|element| element == &repeat)
                    .expect("first occurrence of repeated element");

                assert!(
                    elements[index..index + count]
                        .iter()
                        .all(|element| element == &repeat)
                );
            }
        }

        #[test]
        fn when_odd_number_of_elements_then_sorts_them() {
            for length in (1..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 != 0);

                let mut auxiliary = elements.clone();

                top_down(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_even_number_of_elements_then_sorts_them() {
            for length in (0..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 == 0);

                let mut auxiliary = elements.clone();

                top_down(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_chunks_are_sorted_then_sorts_them_into_rest() {
            for length in 2..255 {
                let mut elements: Vec<_> = (0..256).rev().collect();

                for chunk in elements.chunks_mut(length) {
                    chunk.reverse();

                    debug_assert!(chunk.is_sorted());
                }

                debug_assert!(!elements.is_sorted());

                let mut auxiliary = elements.clone();

                top_down(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }
    }

    mod natural {
        use super::*;

        #[test]
        #[cfg_attr(not(debug_assertions), ignore)]
        #[should_panic = "auxiliary must be clone of elements"]
        fn when_auxiliary_is_not_a_clone_of_elements_then_panics() {
            let mut elements = [5, 4, 3, 2, 1];
            let mut auxiliary = [0, 0, 0, 0, 0];

            natural(&mut elements, &mut auxiliary);
        }

        #[test]
        fn when_empty_then_does_nothing() {
            let mut elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            let mut auxiliary = elements;

            natural(&mut elements, &mut auxiliary);

            assert_eq!(elements, []);
        }

        #[test]
        fn when_single_element_then_does_not_modify_it() {
            for element in 0..256 {
                let mut elements = [element];

                debug_assert_eq!(elements.len(), 1);

                let mut auxiliary = elements;

                natural(&mut elements, &mut auxiliary);

                assert_eq!(elements, [element]);
            }
        }

        #[test]
        fn when_all_elements_are_equivalent_then_does_not_modify_them() {
            for value in 0..256 {
                for length in 2..256 {
                    let mut elements: Vec<_> = core::iter::repeat_n(value, length).collect();

                    debug_assert!(elements.iter().all(|element| element == &value));

                    let mut auxiliary = elements.clone();

                    natural(&mut elements, &mut auxiliary);

                    assert!(elements.into_iter().all(|element| element == value));
                }
            }
        }

        #[test]
        fn when_already_sorted_then_maintains_order() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).collect();

                debug_assert!(elements.is_sorted());

                let mut auxiliary = elements.clone();

                natural(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_in_reverse_sorted_order_then_is_reversed() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.iter().rev().is_sorted());

                let mut auxiliary = elements.clone();

                natural(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_elements_are_repeated_then_they_are_grouped_together() {
            for repeat in 2..128 {
                let mut elements: Vec<_> = (0..256)
                    .map(|element| {
                        if element % repeat == 0 {
                            repeat
                        } else {
                            element
                        }
                    })
                    .collect();

                let count = elements.len().div_ceil(repeat);

                debug_assert_eq!(
                    elements
                        .iter()
                        .filter(|element| *element == &repeat)
                        .count(),
                    count
                );

                let mut auxiliary = elements.clone();

                natural(&mut elements, &mut auxiliary);

                let index = elements
                    .iter()
                    .position(|element| element == &repeat)
                    .expect("first occurrence of repeated element");

                assert!(
                    elements[index..index + count]
                        .iter()
                        .all(|element| element == &repeat)
                );
            }
        }

        #[test]
        fn when_odd_number_of_elements_then_sorts_them() {
            for length in (1..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 != 0);

                let mut auxiliary = elements.clone();

                natural(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_even_number_of_elements_then_sorts_them() {
            for length in (0..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 == 0);

                let mut auxiliary = elements.clone();

                natural(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_chunks_are_sorted_then_sorts_them_into_rest() {
            for length in 2..255 {
                let mut elements: Vec<_> = (0..256).rev().collect();

                for chunk in elements.chunks_mut(length) {
                    chunk.reverse();

                    debug_assert!(chunk.is_sorted());
                }

                debug_assert!(!elements.is_sorted());

                let mut auxiliary = elements.clone();

                natural(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }
    }

    mod bottom_up {
        use super::*;

        #[test]
        #[cfg_attr(not(debug_assertions), ignore)]
        #[should_panic = "auxiliary must be clone of elements"]
        fn when_auxiliary_is_not_a_clone_of_elements_then_panics() {
            let mut elements = [5, 4, 3, 2, 1];
            let mut auxiliary = [0, 0, 0, 0, 0];

            bottom_up(&mut elements, &mut auxiliary);
        }

        #[test]
        fn when_empty_then_does_nothing() {
            let mut elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            let mut auxiliary = elements;

            bottom_up(&mut elements, &mut auxiliary);

            assert_eq!(elements, []);
        }

        #[test]
        fn when_single_element_then_does_not_modify_it() {
            for element in 0..256 {
                let mut elements = [element];

                debug_assert_eq!(elements.len(), 1);

                let mut auxiliary = elements;

                bottom_up(&mut elements, &mut auxiliary);

                assert_eq!(elements, [element]);
            }
        }

        #[test]
        fn when_all_elements_are_equivalent_then_does_not_modify_them() {
            for value in 0..256 {
                for length in 2..256 {
                    let mut elements: Vec<_> = core::iter::repeat_n(value, length).collect();

                    debug_assert!(elements.iter().all(|element| element == &value));

                    let mut auxiliary = elements.clone();

                    bottom_up(&mut elements, &mut auxiliary);

                    assert!(elements.into_iter().all(|element| element == value));
                }
            }
        }

        #[test]
        fn when_already_sorted_then_maintains_order() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).collect();

                debug_assert!(elements.is_sorted());

                let mut auxiliary = elements.clone();

                bottom_up(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_in_reverse_sorted_order_then_is_reversed() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.iter().rev().is_sorted());

                let mut auxiliary = elements.clone();

                bottom_up(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_elements_are_repeated_then_they_are_grouped_together() {
            for repeat in 2..128 {
                let mut elements: Vec<_> = (0..256)
                    .map(|element| {
                        if element % repeat == 0 {
                            repeat
                        } else {
                            element
                        }
                    })
                    .collect();

                let count = elements.len().div_ceil(repeat);

                debug_assert_eq!(
                    elements
                        .iter()
                        .filter(|element| *element == &repeat)
                        .count(),
                    count
                );

                let mut auxiliary = elements.clone();

                bottom_up(&mut elements, &mut auxiliary);

                let index = elements
                    .iter()
                    .position(|element| element == &repeat)
                    .expect("first occurrence of repeated element");

                assert!(
                    elements[index..index + count]
                        .iter()
                        .all(|element| element == &repeat)
                );
            }
        }

        #[test]
        fn when_odd_number_of_elements_then_sorts_them() {
            for length in (1..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 != 0);

                let mut auxiliary = elements.clone();

                bottom_up(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_even_number_of_elements_then_sorts_them() {
            for length in (0..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 == 0);

                let mut auxiliary = elements.clone();

                bottom_up(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_chunks_are_sorted_then_sorts_them_into_rest() {
            for length in 2..255 {
                let mut elements: Vec<_> = (0..256).rev().collect();

                for chunk in elements.chunks_mut(length) {
                    chunk.reverse();

                    debug_assert!(chunk.is_sorted());
                }

                debug_assert!(!elements.is_sorted());

                let mut auxiliary = elements.clone();

                bottom_up(&mut elements, &mut auxiliary);

                assert!(elements.is_sorted());
            }
        }
    }

    mod in_place {
        use super::*;

        #[test]
        fn when_empty_then_does_nothing() {
            let mut elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            in_place(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn when_single_element_then_does_not_modify_it() {
            for element in 0..256 {
                let mut elements = [element];

                debug_assert_eq!(elements.len(), 1);

                in_place(&mut elements);

                assert_eq!(elements, [element]);
            }
        }

        #[test]
        fn when_all_elements_are_equivalent_then_does_not_modify_them() {
            for value in 0..32 {
                for length in 2..32 {
                    let mut elements: Vec<_> = core::iter::repeat_n(value, length).collect();

                    debug_assert!(elements.iter().all(|element| element == &value));

                    in_place(&mut elements);

                    assert!(elements.into_iter().all(|element| element == value));
                }
            }
        }

        #[test]
        fn when_already_sorted_then_maintains_order() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).collect();

                debug_assert!(elements.is_sorted());

                in_place(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_in_reverse_sorted_order_then_is_reversed() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.iter().rev().is_sorted());

                in_place(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_elements_are_repeated_then_they_are_grouped_together() {
            for repeat in 2..128 {
                let mut elements: Vec<_> = (0..256)
                    .map(|element| {
                        if element % repeat == 0 {
                            repeat
                        } else {
                            element
                        }
                    })
                    .collect();

                let count = elements.len().div_ceil(repeat);

                debug_assert_eq!(
                    elements
                        .iter()
                        .filter(|element| *element == &repeat)
                        .count(),
                    count
                );

                in_place(&mut elements);

                let index = elements
                    .iter()
                    .position(|element| element == &repeat)
                    .expect("first occurrence of repeated element");

                assert!(
                    elements[index..index + count]
                        .iter()
                        .all(|element| element == &repeat)
                );
            }
        }

        #[test]
        fn when_odd_number_of_elements_then_sorts_them() {
            for length in (1..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 != 0);

                in_place(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_even_number_of_elements_then_sorts_them() {
            for length in (0..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 == 0);

                in_place(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_chunks_are_sorted_then_sorts_them_into_rest() {
            for length in 2..255 {
                let mut elements: Vec<_> = (0..256).rev().collect();

                for chunk in elements.chunks_mut(length) {
                    chunk.reverse();

                    debug_assert!(chunk.is_sorted());
                }

                debug_assert!(!elements.is_sorted());

                in_place(&mut elements);

                assert!(elements.is_sorted());
            }
        }
    }
}
