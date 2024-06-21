//! Implementations of [Insertion Sort](https://en.wikipedia.org/wiki/Insertion_sort).

pub fn iterative<T: Ord>(elements: &mut [T]) {
    for sorted_length in 1..=elements.len() {
        // The sub-slice is sorted, except for the last element.
        let (sorted, _) = elements.split_at_mut(sorted_length);

        // Move the last element down the list until sorted.
        for unsorted_index in (1..sorted.len()).rev() {
            let Some(previous_index) = unsorted_index.checked_sub(1) else {
                unreachable!("loop stops at index 1, so never zero");
            };

            let (Some(current_element), Some(previous_element)) = (sorted.get(unsorted_index), sorted.get(previous_index)) else {
                unreachable!("loops ensure both indexes are in bounds");
            };

            if current_element < previous_element {
                sorted.swap(unsorted_index, previous_index);
            } else {
                break;
            }
        }
    }
}

pub fn recursive<T: Ord>(elements: &mut [T]) {
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
