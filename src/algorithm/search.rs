//! Implementations of [search](https://en.wikipedia.org/wiki/Search_algorithm).

/// Find the index of `desired` within `elements` using linear search.
///
/// # Methodology
/// The input elements are iterated through and compared against the desired
/// value returning the index of the element if it is equivalent, or none if
/// iteration finishes without finding a match.
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
/// # Methodology
/// An index range is kept whose elements could contain the desired value. The
/// middle element of that range is compared against the desired value: if it
/// is equivalent, then the index is returned; if the desired value is less
/// than the middle element, then the upper bound of the range is updated to be
/// the index; if the desired value is greater than the middle element, then
/// the lower bound of the range is updated to be the index. The range is
/// searched until either a matching element is found, or the lower and upper
/// bounds become equivalent implying the desired element is not contained.
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
    debug_assert!(
        elements.is_sorted(),
        "elements must be sorted in increasing order"
    );

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
        fn is_none_when_input_contains_no_elements() {
            let elements: [usize; 0] = [];

            let actual = linear(&elements, &12345);

            assert_eq!(actual, None);
        }

        #[test]
        fn yields_correct_index_when_contained() {
            const ELEMENTS: usize = 8;

            let elements = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            for desired in 0..ELEMENTS {
                let actual = linear(&elements, &desired);

                assert_eq!(actual, Some(desired));
            }
        }

        #[test]
        fn yields_none_when_not_contained() {
            let elements = [0, 1, 2, 3, 4, 5];

            let actual = linear(&elements, &12345);

            assert_eq!(actual, None);
        }
    }

    mod binary {
        use super::*;

        #[test]
        #[cfg_attr(not(debug_assertions), ignore)]
        #[should_panic = "elements must be sorted in increasing order"]
        fn panics_if_elements_are_not_sorted_in_increasing_order() {
            let elements = [5, 4, 3, 2, 1];

            _ = binary(&elements, &12345);
        }

        #[test]
        fn is_none_when_input_contains_no_elements() {
            let elements: [usize; 0] = [];

            let actual = binary(&elements, &12345);

            assert_eq!(actual, None);
        }

        #[test]
        fn yields_correct_index_when_contained() {
            const ELEMENTS: usize = 8;

            let elements = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            for desired in 0..ELEMENTS {
                let actual = binary(&elements, &desired);

                assert_eq!(actual, Some(desired));
            }
        }

        #[test]
        fn yields_none_when_not_contained_and_would_be_first_element() {
            let elements = [1, 2, 3, 4, 5];

            let actual = binary(&elements, &0);

            assert_eq!(actual, None);
        }

        #[test]
        fn yields_none_when_not_contained_and_would_be_last_element() {
            let elements = [0, 1, 2, 3, 4];

            let actual = binary(&elements, &5);

            assert_eq!(actual, None);
        }

        #[test]
        fn yields_none_when_not_contained_and_would_be_middle_element() {
            let elements = [0, 1, 2, 4, 5];

            let actual = binary(&elements, &3);

            assert_eq!(actual, None);
        }
    }
}
