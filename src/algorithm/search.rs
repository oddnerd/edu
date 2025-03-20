//! Implementations of [search](https://en.wikipedia.org/wiki/Search_algorithm).

/// Find the index of `desired` within `elements` using linear search.
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
/// // Returns `Some` index when found.
/// let index = linear(&slice, &3);
/// assert_eq!(index, Some(3));
///
/// // Returns `None` when not found.
/// let index = linear(&slice, &6);
/// assert_eq!(index, None);
/// ```
pub fn linear<T: PartialEq>(elements: &[T], desired: &T) -> Option<usize> {
    for (index, element) in elements.iter().enumerate() {
        if element == desired {
            return Some(index);
        }
    }

    None
}

/// Find the index of `desired` within `elements` using binary search.
///
/// This method has the precondition that `elements` is sorted, otherwise
/// the result is unspecified and meaningless.
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
/// // Returns `Some` index when found.
/// let index = binary(&slice, &3);
/// assert_eq!(index, Some(3));
///
/// // Returns `None` when not found.
/// let index = binary(&slice, &6);
/// assert_eq!(index, None);
/// ```
pub fn binary<T: Ord + core::fmt::Debug>(elements: &[T], desired: &T) -> Option<usize> {
    debug_assert!(elements.is_sorted(), "required precondition");

    let mut range = 0..elements.len();

    while !range.is_empty() {
        let middle = usize::midpoint(range.start, range.end);

        let Some(element) = elements.get(middle) else {
            unreachable!("range is not empty so index is in bounds");
        };

        range = match element.cmp(desired) {
            core::cmp::Ordering::Equal => return Some(middle),

            core::cmp::Ordering::Greater => range.start..middle,

            #[expect(
                clippy::arithmetic_side_effects,
                reason = "loop ensures middle is at most `usize::MAX - 1` so incremented cannot fail"
            )]
            core::cmp::Ordering::Less => middle + 1..range.end,
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
