//! Implementations of [search](https://en.wikipedia.org/wiki/Search_algorithm).

/// Find the index of `needle` within `haystack` using linear search.
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

/// Find the index of `needle` within `haystack` using binary search.
///
/// # Performance
/// This method takes O(log N) time and consumes O(1) memory.
///
/// # See Also
/// [Wikipedia](https://en.wikipedia.org/wiki/Binary_search).
///
/// # Examples
/// ```
/// use rust::algorithm::search::binary;
///
/// let mut slice = [0, 1, 2, 3, 4, 5];
///
/// let index = binary(&slice, &3);
///
/// assert_eq!(index, Some(3));
/// ```
pub fn binary<T: Ord + core::fmt::Debug>(haystack: &[T], needle: &T) -> Option<usize> {
    let mut left = 0;

    let mut right = haystack.len().checked_sub(1)?;

    while left <= right {
        let offset = left.abs_diff(right) / 2;

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
                // This implies the last element does not match, so not found.
                break;
            };

            left = middle_incremented;
        } else {
            let Some(middle_decremented) = middle.checked_sub(1) else {
                // This implies the first element does not match, so not found.
                break;
            };

            right = middle_decremented;
        }
    }

    None
}

#[cfg(test)]
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
        fn can_find_first_element() {
            let elements = [0, 1, 2, 3, 4, 5];

            assert_eq!(linear(&elements, &0), Some(0));
        }

        #[test]
        fn can_find_last_element() {
            let elements = [0, 1, 2, 3, 4, 5];

            assert_eq!(linear(&elements, &5), Some(5));
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
        fn can_find_first_element() {
            let elements = [0, 1, 2, 3, 4, 5];

            assert_eq!(binary(&elements, &0), Some(0));
        }

        #[test]
        fn can_find_last_element() {
            let elements = [0, 1, 2, 3, 4, 5];

            assert_eq!(binary(&elements, &5), Some(5));
        }

        #[test]
        fn yields_none_when_not_contained() {
            let elements = [0, 1, 2, 3, 4, 5];

            assert_eq!(binary(&elements, &6), None);
        }
    }
}
