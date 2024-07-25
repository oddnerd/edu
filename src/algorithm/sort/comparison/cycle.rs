//! Implementations of [Cycle Sort](https://en.wikipedia.org/wiki/Cycle_sort).

/// TODO
pub(super) fn cycle<T: Ord + Clone>(elements: &mut [T]) {
    for current in 0..elements.len() {
        let Some(mut item) = elements.get(current).cloned() else {
            unreachable!("loop ensures index is within bounds");
        };

        let mut sorted_index = current + elements[current + 1..].iter().filter(|element| element < &&item).count();

        if sorted_index == current {
            continue;
        }

        for element in &elements[sorted_index..] {
            if element == &item {
                sorted_index += 1;
            } else {
                break;
            }
        }

        core::mem::swap(&mut item, &mut elements[sorted_index]);

        while sorted_index != current {
            sorted_index = current + elements[current + 1..].iter().filter(|element| element < &&item).count();

            while item == elements[sorted_index] {
                sorted_index += 1;
            }

            core::mem::swap(&mut item, &mut elements[sorted_index]);
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
