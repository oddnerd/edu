//! Implementations of [Selection Sort](https://en.wikipedia.org/wiki/Selection_sort).

/// Sort `elements` using iterative selection sort.
///
/// Note that this is non-stable meaning the order of equivalent elements is
/// not preserved.
///
/// Iterate through the unsorted elements to select the minimum value, swapping
/// it to the beginning of the unsorted list which is its sorted position. The
/// unsorted list can then be reduced to exclude this first element, repeating
/// until there are no elements left to be sorted.
///
/// # Performance
/// This method takes O(N<sup>2</sup>) time and consumes O(1) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::selection::iterative;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// iterative(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn iterative<T: Ord>(elements: &mut [T]) {
    for sorted in 0..elements.len() {

        let (_, unsorted) = elements.split_at_mut(sorted);

        let Some((current, rest)) = unsorted.split_first_mut() else {
            unreachable!("loop ensures there is at least one element");
        };

        for element in rest {
            if element < current {
                core::mem::swap(current, element);
            }
        }
    }
}

/// Sort `elements` using stable selection sort.
///
/// Almost identical to traditional [`iterative`] solution, except the minimum
/// element is moved into sorted position via a rotation instead of a swap.
///
/// # Performance
/// This method takes O(N<sup>3</sup>) time and consumes O(1) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::selection::stable;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// stable(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn stable<T: Ord>(elements: &mut [T]) {
    for sorted in 0..elements.len() {
        let mut minimum_index = sorted;

        // Find the minimum elements within the unsorted range.
        for current_index in sorted..elements.len() {
            let Some(minimum_element) = elements.get(minimum_index) else {
                unreachable!("loop ensures index is within bounds");
            };

            let Some(current_element) = elements.get(current_index) else {
                unreachable!("loop ensures index is within bounds");
            };

            if current_element < minimum_element {
                minimum_index = current_index;
            }
        }

        // Place the minimum element into sorted position, maintaining order.
        let Some(shifted) = elements.get_mut(sorted..=minimum_index) else {
            unreachable!("loop ensures range is within bounds");
        };

        shifted.rotate_right(1);
    }
}

/// Sort `elements` using bidirectional selection sort.
///
/// Note that this is non-stable meaning the order of equivalent elements is
/// not preserved.
///
/// Unlike the traditional [`iterative`] solution which only selects the
/// minimum elements and swaps them to the beginning of the list, this
/// variation finds both the minimum and maximum value whilst iterating through
/// the list placing the minimum at the beginning and the maximum and the end
/// with a decreasing section of unsorted elements in the middle.
///
/// # Performance
/// This method takes O(N<sup>2</sup>) time and consumes O(1) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::selection::bidirectional;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// bidirectional(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn bidirectional<T: Ord>(elements: &mut [T]) {
    for sorted in 0..(elements.len() / 2) {
        let Some(last_sorted) = elements.len().checked_sub(sorted) else {
            unreachable!("loop ensures `sorted < elements.len()`");
        };

        let Some(unsorted) = elements.get_mut(sorted..last_sorted) else {
            unreachable!("loop ensures range is in bounds");
        };

        let Some((minimum, unsorted)) = unsorted.split_first_mut() else {
            unreachable!();
        };

        let Some((maximum, unsorted)) = unsorted.split_last_mut() else {
            unreachable!();
        };

        if minimum > maximum {
            core::mem::swap(minimum, maximum);
        }

        for element in unsorted {
            #[allow(clippy::else_if_without_else)]
            if element < minimum {
                core::mem::swap(element, minimum);
            } else if element > maximum {
                core::mem::swap(element, maximum);
            }
        }
    }
}

pub fn bingo<T: Ord + core::fmt::Debug>(elements: &mut [T]) {
    // Assume the first element is the minimum.
    let mut minimum_index = 0;

    // Find the overall minimum value.
    for (current_index, current_element) in elements.iter().enumerate() {
        let Some(minimum_element) = elements.get(minimum_index) else {
            unreachable!("loop ensures index is within bounds");
        };

        if current_element < minimum_element {
            minimum_index = current_index;
        }
    }

    let mut split_index = 0;
    while split_index < elements.len() {
        // Place the first value into position so it can be compared against.
        elements.swap(split_index, minimum_index);

        if let Some(incremented) = split_index.checked_add(1) {
            split_index = incremented;
        } else {
            unreachable!("while-loop prevents overflow");
        }

        let (sorted, unsorted) = elements.split_at_mut(split_index);

        let Some(minimum_element) = sorted.last() else {
            unreachable!("the first minimum value was placed into position");
        };

        // Note the minimum for the next iteration whilst sorting the current.
        let mut next_minimum_index = None::<usize>;

        // How many elements from `unsorted` that have been sorted.
        let mut output_index = 0;

        for current_index in 0..unsorted.len() {
            let Some(current_element) = unsorted.get(current_index) else {
                unreachable!("for-loop ensures index is within bounds");
            };

            if current_element == minimum_element {
                unsorted.swap(output_index, current_index);

                // Outputting the current element overwrote the next minimum.
                if next_minimum_index.is_some_and(|index| index == output_index) {
                    next_minimum_index = Some(current_index);
                }

                if let Some(incremented) = output_index.checked_add(1) {
                    output_index = incremented;
                } else {
                    unreachable!("for-loop ensures index cannot overflow");
                }
            } else if let Some(index) = next_minimum_index {
                let Some(next_minimum_element) = unsorted.get(index) else {
                    unreachable!("for-loop ensures index is within bounds");
                };

                if current_element < next_minimum_element {
                    next_minimum_index = Some(current_index);
                }
            } else {
                next_minimum_index = Some(current_index);
            }
        }

        // Update the minimum to the one found during this iteration.
        if let Some(offset) = next_minimum_index {
            let Some(index) = offset.checked_add(split_index) else {
                unreachable!("index of a specific element, so fits in usize");
            };

            minimum_index = index;
        } else {
            debug_assert_eq!(split_index, elements.len(), "all sorted");
            break;
        }

        // Update the split between sorted and unsorted elements.
        if let Some(incremented) = split_index.checked_add(output_index) {
            split_index = incremented;
        } else {
            unreachable!("at most the number of elements, so fits in usize");
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
        fn empty() {
            let mut elements: [usize; 0] = [];

            iterative(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            iterative(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            iterative(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            iterative(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            iterative(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            iterative(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod stable {
        use super::*;

        #[test]
        fn empty() {
            let mut elements: [usize; 0] = [];

            stable(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            stable(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            stable(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            stable(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            stable(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            stable(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod bidirectional {
        use super::*;

        #[test]
        fn empty() {
            let mut elements: [usize; 0] = [];

            bidirectional(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            bidirectional(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            bidirectional(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            bidirectional(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            bidirectional(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            bidirectional(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod bingo {
        use super::*;

        #[test]
        fn empty() {
            let mut elements: [usize; 0] = [];

            bingo(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            bingo(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            bingo(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            bingo(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            bingo(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            bingo(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }
}
