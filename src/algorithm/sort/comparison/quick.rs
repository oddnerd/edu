//! Implementations of [Quick Sort](https://en.wikipedia.org/wiki/Quicksort).

/// Sort `elements` using quick sort with Lomuto's partition scheme.
///
/// Note that this is non-stable meaning the order of equivalent elements is
/// not preserved.
///
/// Place the last element into sorted order by partitioning, i.e., placing
/// smaller elements before it and greater elements after it. Recursively sort
/// the remaining unsorted sub-lists placing one element into sorted order for
/// each call until all elements are sorted.
///
/// # Performance
/// This method takes O(N<sup>2</sup>) time and consumes O(N) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::quick::lomuto;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// lomuto(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn lomuto<T: Ord>(elements: &mut [T]) {
    /// Partition `elements` based on the last element.
    ///
    /// This places the last element into sorted position, as well as ordering
    /// the remaining elements such that those less than it come before and
    /// those greater come after.
    fn partition<T: Ord>(elements: &mut [T]) -> usize {
        let Some((pivot_element, elements)) = elements.split_last_mut() else {
            unreachable!("caller is responsible for ensuring not empty");
        };

        // The sorted position for the pivot element.
        let mut pivot_index = 0;

        for index in 0..elements.len() {
            let Some(element) = elements.get(index) else {
                unreachable!("loop ensures index is within bounds");
            };

            if element <= pivot_element {
                elements.swap(index, pivot_index);

                if let Some(incremented) = pivot_index.checked_add(1) {
                    pivot_index = incremented;
                } else {
                    unreachable!("loop ensures index cannot overflow");
                }
            }
        }

        if let Some(temporary_pivot) = elements.get_mut(pivot_index) {
            core::mem::swap(temporary_pivot, pivot_element);
        } else {
            debug_assert_eq!(
                pivot_index,
                elements.len(),
                "pivot is already sorted as the last overall element"
            );
        }

        pivot_index
    }

    if elements.len() <= 1 {
        return;
    }

    // Place the pivot element into sorted position.
    let pivot = partition(elements);

    let (left, right) = elements.split_at_mut(pivot);

    let Some((_pivot, right)) = right.split_first_mut() else {
        unreachable!("contains at least the pivot element");
    };

    lomuto(left);
    lomuto(right);
}

pub fn hoare<T: Ord>(elements: &mut [T]) {
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

    mod lomuto {
        use super::*;

        #[test]
        fn empty() {
            let mut elements: [usize; 0] = [];

            lomuto(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            lomuto(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            lomuto(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            lomuto(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            lomuto(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            lomuto(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod hoare {
        use super::*;

        #[test]
        fn empty() {
            let mut elements: [usize; 0] = [];

            hoare(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            hoare(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            hoare(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            hoare(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            hoare(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            hoare(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }
}
