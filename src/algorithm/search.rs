//! Implementations of [search](https://en.wikipedia.org/wiki/Search_algorithm).

/// Find the index of `desired` within `elements` using linear search.
///
/// # Algorithm
/// The input elements are iterated through and compared against the desired
/// value returning the index of the element if it is equivalent, or none if
/// iteration finishes without finding a match.
///
/// # Performance
/// This algorithm always consumes O(1) memory but has varying time complexity
/// depending on the input. The best-case is when the desired is the first
/// element taking O(1) times, the worst-case is when the desired is the last
/// elements taking O(N) times, and the average is O(N) time.
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
/// <div class="warning">
/// If `elements` is not sorted increasingly, the result is unspecified.
/// </div>
///
/// # Algorithm
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
/// This algorithm always consumes O(1) memory but has varying time complexity
/// depending on the input. The best-case is when the desired is the middle
/// elements taking O(1) time, the worst-case is when the desired is the first
/// or last elements taking O(log N) time, and the average is O(log N) time.
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
        fn when_elements_is_empty_then_yields_none() {
            let elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            let actual = linear(&elements, &12345);

            assert_eq!(actual, None);
        }

        #[test]
        fn when_element_is_not_contained_then_yields_none() {
            let elements = [0, 1, 2, 3, 4, 5];

            let actual = linear(&elements, &12345);

            assert_eq!(actual, None);
        }

        #[test]
        fn when_elements_is_contained_then_yields_correct_index() {
            const ELEMENTS: usize = 256;

            let elements = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            for desired in 0..ELEMENTS {
                let actual = linear(&elements, &desired);

                assert_eq!(actual, Some(desired));
            }
        }
    }

    mod binary {
        use super::*;

        #[test]
        #[cfg_attr(not(debug_assertions), ignore)]
        #[should_panic = "elements must be sorted in increasing order"]
        fn when_elements_is_not_sorted_in_increasing_order_then_panics() {
            let elements = [5, 4, 3, 2, 1];

            debug_assert!(!elements.is_sorted());

            _ = binary(&elements, &12345);
        }

        #[test]
        fn when_elements_is_empty_then_yields_none() {
            let elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            let actual = binary(&elements, &12345);

            assert_eq!(actual, None);
        }

        #[test]
        fn when_elements_is_contained_then_yields_correct_index() {
            const ELEMENTS: usize = 256;

            let elements = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            for desired in 0..ELEMENTS {
                let actual = binary(&elements, &desired);

                assert_eq!(actual, Some(desired));
            }
        }

        #[test]
        fn when_element_is_not_contained_then_yields_none() {
            for desired in 0..256 {
                let mut elements: Vec<_> = (0..256).collect();

                _ = elements.remove(desired);

                assert_eq!(binary(&elements, &desired), None);
            }
        }
    }
}
