//! Implementations of [Cycle Sort](https://en.wikipedia.org/wiki/Cycle_sort).

/// TODO
pub(super) fn cycle<T: Ord + Clone>(elements: &mut [T]) {
    for start in 0..elements.len() {
        let Some(mut item) = elements.get(start).cloned() else {
            unreachable!("loop ensures index is within bounds");
        };

        let mut pos = start;

        for i in (start + 1)..elements.len() {
            if elements[i] < item {
                pos += 1;
            }
        }

        if pos == start {
            continue;
        }

        while item == elements[pos] {
            pos += 1;
        }

        core::mem::swap(&mut item, &mut elements[pos]);

        while pos != start {
            pos = start;

            for i in (start + 1)..elements.len() {
                if elements[i] < item {
                    pos += 1;
                }
            }

            while item == elements[pos] {
                pos += 1;
            }

            core::mem::swap(&mut item, &mut elements[pos]);
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
