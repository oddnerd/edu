//! Implementations of [search](https://en.wikipedia.org/wiki/Search_algorithm).

/// Find the index corresponding to an element with particular value.
///
/// # Performance
/// This method takes O(N) time and consumes O(1) memory.
///
/// # See Also
/// [Wikipedia](https://en.wikipedia.org/wiki/Linear_search).
///
/// # Examples
/// ```
/// use rust::algorithm::search::linear;
///
/// let mut slice = [0, 1, 2, 3, 4, 5];
///
/// let index = linear(&slice, &3);
///
/// assert_eq!(index, Some(3));
/// ```
pub fn linear<T: PartialEq>(haystack: &[T], needle: &T) -> Option<usize> {
    for (index, element) in haystack.iter().enumerate() {
        if element == needle {
            return Some(index);
        }
    }

    None
}

pub fn binary<T: Ord + core::fmt::Debug>(haystack: &[T], needle: &T) -> Option<usize> {
    let mut left = 0;

    let mut right = haystack.len().checked_sub(1)?;

    while left <= right {
        let offset = left.abs_diff(right).div_ceil(2);

        let Some(middle) = left.checked_add(offset) else {
            unreachable!("at most equal to right, hence cannot overflow");
        };

        let Some(current) = haystack.get(middle) else {
            unreachable!("loop ensures index is within bounds");
        };

        if current == needle {
            return Some(middle);
        }

        if current < needle {
            let Some(middle_incremented) = middle.checked_add(1) else {
                break;
            };

            left = middle_incremented;
        } else {
            let Some(middle_decremented) = middle.checked_sub(1) else {
                break;
            };

            right = middle_decremented;
        }
    }

    None
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
