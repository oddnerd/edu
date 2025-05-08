//! Implementation of miscellaneous (no variation) sorting algorithms.

/// Sort `elements` via cycle sort.
///
/// <div class="warning">
/// This is unstable so the order of equivalent elements is not guaranteed.
/// </div>
///
/// # Algorithm
/// Iterating from left to right, find the sorted position of the current
/// element by counting how many elements to the right are less than it.
/// Iteratively swap it into sorted position (at the end of any run of
/// equivalent elements already in sorted position) until the element whose
/// sorted position is at the current position is swapped into the current
/// position.
///
/// # Performance
/// This algorithm consumes O(1) memory and has O(N<sup>2</sup>) time
/// complexity regardless of input.
///
/// # See Also
/// [Wikipedia](https://en.wikipedia.org/wiki/Cycle_sort).
///
/// # Examples
/// ```
/// use rust::algorithm::sort::misc::cycle;
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

        #[expect(clippy::shadow_unrelated, reason = "current is `elements[current]`")]
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
mod test {
    use super::*;

    mod cycle {
        use super::*;

        #[test]
        fn when_empty_then_does_nothing() {
            let mut elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            cycle(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn when_single_element_then_does_not_modify_it() {
            for element in 0..256 {
                let mut elements = [element];

                debug_assert_eq!(elements.len(), 1);

                cycle(&mut elements);

                assert_eq!(elements, [element]);
            }
        }

        #[test]
        fn when_all_elements_are_equivalent_then_does_not_modify_them() {
            for value in 0..256 {
                for length in 2..256 {
                    let mut elements: Vec<_> = core::iter::repeat_n(value, length).collect();

                    debug_assert!(elements.iter().all(|element| element == &value));

                    cycle(&mut elements);

                    assert!(elements.into_iter().all(|element| element == value));
                }
            }
        }

        #[test]
        fn when_already_sorted_then_maintains_order() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).collect();

                debug_assert!(elements.is_sorted());

                cycle(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_in_reverse_sorted_order_then_is_reversed() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.iter().rev().is_sorted());

                cycle(&mut elements);

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

                cycle(&mut elements);

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

                cycle(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_even_number_of_elements_then_sorts_them() {
            for length in (0..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 == 0);

                cycle(&mut elements);

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

                cycle(&mut elements);

                assert!(elements.is_sorted());
            }
        }
    }
}
