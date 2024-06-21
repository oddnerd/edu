//! Implementations of [Insertion Sort](https://en.wikipedia.org/wiki/Insertion_sort).

/// Sort `elements` using iterative insertion sort.
///
/// Starting from the first element of the slice which in isolation is a sorted
/// subsection, iteratively move the element to the right of the sorted
/// section to the left into sorted position within the sorted section
/// until all elements have been moved into the sorted section.
///
/// # Performance
/// This method takes O(N<sup>2</sup>) time and consumes O(1) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::insertion::iterative;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// iterative(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn iterative<T: Ord>(elements: &mut [T]) {
    for sorted_length in 2..=elements.len() {
        // The sub-slice is sorted, except for the last element.
        let (sorted, _) = elements.split_at_mut(sorted_length);

        // Move the last element down the list until sorted.
        for unsorted_index in (1..sorted.len()).rev() {
            let Some(before_index) = unsorted_index.checked_sub(1) else {
                unreachable!("loop stops at index 1, so never zero");
            };

            let (Some(current_element), Some(before_element)) = (sorted.get(unsorted_index), sorted.get(before_index)) else {
                unreachable!("loops ensure both indexes are in bounds");
            };

            if current_element < before_element {
                sorted.swap(unsorted_index, before_index);
            } else {
                break;
            }
        }
    }
}

/// Sort `elements` using recursive insertion sort.
///
/// Recursively sort all but the last element, then move the last element
/// to the left into sorted position within the sorted section.
///
/// # Performance
/// This method takes O(N<sup>2</sup>) time and consumes O(N) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::insertion::recursive;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// recursive(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn recursive<T: Ord>(elements: &mut [T]) {
    let Some((_last, remaining)) = elements.split_last_mut() else {
        debug_assert_eq!(elements.len(), 0, "only condition it is none");
        return;
    };

    // Sort everything except the last element.
    recursive(remaining);

    // Move the last element down the list until sorted.
    for unsorted_index in (1..elements.len()).rev() {
        let Some(before_index) = unsorted_index.checked_sub(1) else {
            unreachable!("loop stops at index 1, so never zero");
        };

        let (Some(current_element), Some(before_element)) = (elements.get(unsorted_index), elements.get(before_index)) else {
            unreachable!("loops ensure both indexes are in bounds");
        };

        if current_element < before_element {
            elements.swap(unsorted_index, before_index);
        } else {
            break;
        }
    }
}

pub fn binary<T: Ord>(elements: &mut [T]) {
    todo!()
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
            let mut elements = [usize::default(); 0];

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

    mod recursive {
        use super::*;

        #[test]
        fn empty() {
            let mut elements = [usize::default(); 0];

            recursive(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            recursive(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            recursive(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            recursive(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            recursive(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            recursive(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }
}
