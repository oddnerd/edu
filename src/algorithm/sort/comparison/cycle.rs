//! Implementations of [Cycle Sort](https://en.wikipedia.org/wiki/Cycle_sort).

/// TODO
pub(super) fn cycle<T: Ord + Clone>(elements: &mut [T]) {
    for current in 0..elements.len() {
        let (_sorted, unsorted) = elements.split_at_mut(current);

        #[allow(clippy::shadow_unrelated)]
        let Some((current, rest)) = unsorted.split_first_mut() else {
            unreachable!("loop ensures at least one element contained");
        };

        let offset = rest.iter().filter(|element| element < &&*current).count();

        let Some(mut offset) = offset.checked_sub(1) else {
            continue;
        };

        let equivalent = rest[offset..].iter().take_while(|element| element == &current).count();

        offset += equivalent;

        core::mem::swap(current, &mut rest[offset]);

        while offset != 0 {
            offset = rest.iter().filter(|element| element < &&*current).count();

            if let Some(decrement) = offset.checked_sub(1) {
                offset = decrement;
            } else {
                break;
            }

            #[allow(clippy::shadow_unrelated)]
            let equivalent = rest[offset..].iter().take_while(|element| element == &current).count();

            offset += equivalent;

            core::mem::swap(current, &mut rest[offset])
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
