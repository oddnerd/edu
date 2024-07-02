//! Implementations of [Quick Sort](https://en.wikipedia.org/wiki/Quicksort).

/// TODO
pub fn lomuto<T: Ord + Clone>(elements: &mut [T]) {
    /// TODO
    fn partition<T: Ord + Clone>(elements: &mut [T]) -> usize {
        let Some((pivot, remaining)) = elements.split_last_mut() else {
            unreachable!("caller is responsible for ensuring not empty");
        };

        let mut pivot_index = 0;

        for current_index in 0..remaining.len() {
            let Some(current_elements) = remaining.get(current_index) else {
                unreachable!("loop ensures index is within bounds");
            };

            if current_elements <= pivot {
                remaining.swap(current_index, pivot_index);

                if let Some(incremented) = pivot_index.checked_add(1) {
                    pivot_index = incremented;
                } else {
                    unreachable!("loop ensures index cannot overflow");
                }
            }
        }

        elements.swap(pivot_index, elements.len() - 1);

        pivot_index
    }

    if elements.len() <= 1 {
        return;
    }

    let pivot = partition(elements);

    let (left, right) = elements.split_at_mut(pivot);

    let Some((_, right)) = right.split_first_mut() else {
        todo!();
    };

    lomuto(left);
    lomuto(right);
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
}
