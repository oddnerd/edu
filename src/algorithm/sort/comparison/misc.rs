//! Implementation of miscellaneous (no variation) sorting algorithms.

/// Sort `elements` using cycle sort.
///
/// Note that this is non-stable meaning the order of equivalent elements is
/// not preserved.
///
/// From left to right, find the sorted position of the current element by
/// counting how many elements to the right are less-than it. Iteratively swap
/// it into sorted position (at the end of any run of equivalent elements
/// already in sorted position) until the element whose sorted position is at
/// the current position is swapped into the current position.
///
/// # Performance
/// This method takes O(N<sup>2</sup>) time and consumes O(1) memory.
///
/// # See Also
/// [Wikipedia](https://en.wikipedia.org/wiki/Cycle_sort).
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::misc::cycle;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// cycle(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn cycle<T: Ord>(elements: &mut [T]) {
    for current in 0..elements.len() {
        let (_sorted, unsorted) = elements.split_at_mut(current);

        #[allow(clippy::shadow_unrelated)]
        let Some((current, rest)) = unsorted.split_first_mut() else {
            unreachable!("loop ensures at least one element contained");
        };

        loop {
            // How far distance to move current element into sorted position.
            let distance = rest.iter().filter(|element| element < &&*current).count();

            // Index of sorted position for current element.
            let Some(sorted) = distance.checked_sub(1) else {
                break;
            };

            // Outputting into run of equivalent elements causes infinite loop.
            let (_, output) = rest.split_at_mut(sorted);

            // How many in sorted position equivalent to the current element.
            let offset = output
                .iter()
                .take_while(|element| element == &current)
                .count();

            let Some(output) = output.get_mut(offset) else {
                unreachable!("the element was not already in sorted position");
            };

            // Place the element into last possible sorted position.
            core::mem::swap(current, output);
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

    mod cycle {
        use super::*;

        #[test]
        fn empty() {
            let mut elements: [usize; 0] = [];

            cycle(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            cycle(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            cycle(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            cycle(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            cycle(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            cycle(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }
}
