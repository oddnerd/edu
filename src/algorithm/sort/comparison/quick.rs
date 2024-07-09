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
/// This partition scheme averages three times the swaps of [`hoare`].
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
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
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

/// Sort `elements` using quick sort with Hoare's partition scheme.
///
/// Note that this is non-stable meaning the order of equivalent elements is
/// not preserved.
///
/// Partition the elements into two subregions with the left containing all
/// elements less than or greater to the first element, and the right
/// containing all elements greater. Recursively sort these subregions until
/// only a single element is contained thereby placing it into sorted position.
///
/// This partition scheme averages 1/3 the swaps of [`lomuto`].
///
/// # Performance
/// This method takes O(N<sup>2</sup>) time and consumes O(N) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::quick::hoare;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// hoare(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn hoare<T: Ord>(elements: &mut [T]) {
    /// Partition `elements` based on the first element.
    ///
    /// Returns some `index` such that all elements within `[..index]` are less
    /// than the first element, and all elements within `[index..]` are
    /// greater. Note that this does not imply the first element is within
    /// sorted position.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn partition<T: Ord>(elements: &mut [T]) -> usize {
        // Arbitrarily set pivot to first element.
        let mut pivot_index = 0;

        let mut left = 0;

        let Some(mut right) = elements.len().checked_sub(1) else {
            unreachable!("caller ensures elements is not empty");
        };

        loop {
            let Some(pivot_element) = elements.get(pivot_index) else {
                unreachable!("loops ensures pivot is within bounds")
            };

            // Find leftmost element that should be to the right of the pivot.
            while elements
                .get(left)
                .is_some_and(|element| element < pivot_element)
            {
                if let Some(incremented) = left.checked_add(1) {
                    left = incremented;
                } else {
                    break;
                }
            }

            // Find rightmost element that should be to the left of the pivot.
            while elements
                .get(right)
                .is_some_and(|element| element > pivot_element)
            {
                if let Some(decremented) = right.checked_sub(1) {
                    right = decremented;
                } else {
                    break;
                }
            }

            if left < right {
                // This swap might move the pivot element.
                #[allow(clippy::else_if_without_else)]
                if pivot_index == left {
                    pivot_index = right;
                } else if pivot_index == right {
                    pivot_index = left;
                }

                // Swap left and right to be correct side of pivot.
                elements.swap(left, right);

                if let (Some(incremented), Some(decremented)) =
                    (left.checked_add(1), right.checked_sub(1))
                {
                    left = incremented;
                    right = decremented;
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        right.checked_add(1).unwrap_or_else(|| {
            unreachable!("will be a valid index, so at most `usize::MAX - 1`");
        })
    }

    if elements.len() <= 1 {
        return;
    }

    let pivot = partition(elements);

    let (left, right) = elements.split_at_mut(pivot);

    hoare(left);
    hoare(right);
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
