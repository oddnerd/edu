//! Implementations of [search](https://en.wikipedia.org/wiki/Search_algorithm).

fn linear<T: Ord>(haystack: &[T], needle: &T) -> Option<usize> {
    for (index, element) in haystack.iter().enumerate() {
        if element == needle {
            return Some(index);
        }
    }

    None
}

fn binary<T: Ord>(haystack: &[T], needle: &T) -> Option<usize> {
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

    mod linear {
        use super::*;

        #[test]
        fn empty() {
            let elements: [usize; 0] = [];

            assert_eq!(linear(&elements, &0), None);
        }

        #[test]
        fn yields_correct_index_when_contained() {
            let elements = [0, 1, 2, 3, 4, 5];

            assert_eq!(linear(&elements, &2), Some(2));
        }

        #[test]
        fn yields_none_when_not_contained() {
            let elements = [0, 1, 2, 3, 4, 5];

            assert_eq!(linear(&elements, &6), None);
        }
    }

    mod binary {
        use super::*;

        #[test]
        fn empty() {
            let elements: [usize; 0] = [];

            assert_eq!(binary(&elements, &0), None);
        }

        #[test]
        fn yields_correct_index_when_contained() {
            let elements = [0, 1, 2, 3, 4, 5];

            assert_eq!(binary(&elements, &2), Some(2));
        }

        #[test]
        fn yields_none_when_not_contained() {
            let elements = [0, 1, 2, 3, 4, 5];

            assert_eq!(binary(&elements, &6), None);
        }
    }
}
