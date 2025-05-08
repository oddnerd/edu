//! Implementations of [Quick Sort](https://en.wikipedia.org/wiki/Quicksort).

/// Sort `elements` via quicksort according to some `partition` scheme.
///
/// The provided `partition` function must divide `elements` into two
/// sub-slices such that all elements of the left sub-slice are less-than or
/// equal to all elements of the right sub-slice. It takes an index to a
/// contained `pivot` element which is recommended as the value dividing the
/// left and right partitions such that all left elements are less-than or
/// equal to the pivot and all right elements are greater-than or equal to
/// the pivot.
fn recurse<T: Ord>(
    elements: &mut [T],
    partition: &impl Fn(&mut [T], usize) -> (&mut [T], &mut [T]),
) {
    if elements.len() <= 1 {
        return;
    }

    let (Some(first), Some(mid), Some(last)) = (
        elements.first(),
        elements.get(elements.len() / 2),
        elements.last(),
    ) else {
        unreachable!("there is at least one element");
    };

    // Pivot can be any arbitrary element such as the first, middle, or last.
    // This selects the median of those three therefore most likely creating
    // equally sized partitions thereby evenly dividing work for subsequent
    // recursive calls. Note that not-equals is logically exclusive or.
    let pivot = if (first > mid) != (first > last) {
        0
    } else if (mid < first) != (mid < last) {
        elements.len() / 2
    } else {
        elements
            .len()
            .checked_sub(1)
            .unwrap_or_else(|| unreachable!("there is at least one element"))
    };

    // Split the input into two partition based on the pivot.
    let (left, right) = partition(elements, pivot);

    // Assuming tail recursive optimization whereby the last call reuses the
    // stack frame of this current call, forking for the smaller partition
    // first and then tail-recursing into the larger ensures O(log N) call
    // stack space (and therefore memory) consumed. However, note that this
    // optimization is not explicitly guaranteed hence this technically still
    // has O(N) memory requirement.
    if left.len() < right.len() {
        recurse(left, partition);
        recurse(right, partition);
    } else {
        recurse(right, partition);
        recurse(left, partition);
    }
}

/// Sort `elements` via quick sort with Hoare's partition scheme.
///
/// <div class="warning">
/// This is unstable so the order of equivalent elements is not guaranteed.
/// </div>
///
/// # Algorithm
/// Place an element (the pivot) into sorted position by partitioning the
/// elements on it, i.e., placing smaller elements before it and larger
/// elements after. This is accomplished by iteratively swapping the leftmost
/// element that should be right of the pivot and the rightmost element that
/// should be left of the pivot until they meet which is the sorted position
/// for the pivot. The resulting partitions can then be independently
/// recursively sorted since all elements of the left partition are less-than
/// or equal to all elements within the right partition.
///
/// Compared to [`lomuto`], this implementation makes fewer swaps and evenly
/// partitions runs of equivalent elements. However, unlike [`three_way`],
/// elements equivalent to the pivot (which were sorted by partition) are still
/// included in the partitions recursively sorted.
///
/// # Performance
/// This algorithm always consumes O(log N) memory but has varying time
/// complexity depending on the input. The best-case occurs when the partition
/// evenly divides the input into two sub-slices containing the same number of
/// elements taking 𝛀(N ⋅ log N), the worst-case occurs when the partition
/// separates a single element from the rest taking O(N<sup>2</sup>), and the
/// average is 𝚯(N ⋅ log N) time.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::quick::hoare;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// hoare(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn hoare<T: Ord>(elements: &mut [T]) {
    recurse(elements, &|partition, pivot| {
        debug_assert!(pivot < partition.len(), "pivot must be within bounds");

        // Ensure pivot is first element.
        partition.swap(pivot, 0);

        let mut left = 1;
        let mut right = partition
            .len()
            .checked_sub(1)
            .unwrap_or_else(|| unreachable!("caller ensures there is at least one element"));

        loop {
            #[expect(
                clippy::shadow_unrelated,
                reason = "pivot element was swapped to front"
            )]
            let Some(pivot) = partition.first() else {
                unreachable!("caller ensures there is at least one element");
            };

            // Find the leftmost element that should be right of the pivot.
            while left < right && partition.get(left).is_some_and(|element| element < pivot) {
                if let Some(incremented) = left.checked_add(1) {
                    left = incremented;
                } else {
                    break;
                }
            }

            // Find the rightmost element that should be left of the pivot.
            while 0 < right && partition.get(right).is_some_and(|element| element > pivot) {
                if let Some(decremented) = right.checked_sub(1) {
                    right = decremented;
                } else {
                    break;
                }
            }

            if left < right {
                // Swap the left and right elements onto correct side of pivot.
                partition.swap(left, right);

                // Prevent infinite loop upon equivalent elements.
                if let (Some(incremented), Some(decremented)) =
                    (left.checked_add(1), right.checked_sub(1))
                {
                    left = incremented;
                    right = decremented;
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        // Place pivot element into sorted position.
        partition.swap(0, right);

        #[expect(clippy::shadow_unrelated, reason = "derived from left/right indexes")]
        let (left, right) = partition.split_at_mut(right);

        // Ignore pivot in recursive calls since it is already sorted.
        let Some((_pivot, right)) = right.split_first_mut() else {
            unreachable!("contains at least the pivot element");
        };

        (left, right)
    });
}

/// Sort `elements` via quick sort with Lomuto's partition scheme.
///
/// <div class="warning">
/// This is unstable so the order of equivalent elements is not guaranteed.
/// </div>
///
/// # Algorithm
/// Place an element into sorted position by partitioning the elements on it,
/// i.e., placing smaller elements before it and larger elements after. This is
/// accomplished by placing the selected element at the front and then
/// iteratively swapping the first element with any subsequent smaller element.
/// The resulting partitions can then be independently recursively sorted since
/// all elements of the left partition are less-than or equal to all elements
/// within the right partition.
///
/// This implementation averages three time the swaps of [`hoare`] and does not
/// evenly partition strings of equivalent elements.
///
/// # Performance
/// This algorithm always consumes O(N) memory but has varying time
/// complexity depending on the input. The best-case occurs when the partition
/// evenly divides the input into two sub-slices containing the same number of
/// elements taking 𝛀(N ⋅ log N), the worst-case occurs when the partition
/// separates a single element from the rest taking O(N<sup>2</sup>), and the
/// average is 𝚯(N ⋅ log N) time.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::quick::lomuto;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// lomuto(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn lomuto<T: Ord>(elements: &mut [T]) {
    recurse(elements, &|partition, pivot| {
        debug_assert!(pivot < partition.len(), "pivot must be within bounds");

        // Ensure pivot is the first element.
        partition.swap(pivot, 0);

        // Find the index that divides the two partitions.
        let mut mid: usize = 0;

        for current in 1..partition.len() {
            let Some(element) = partition.get(current) else {
                unreachable!("loop ensures index is within bounds");
            };

            #[expect(
                clippy::shadow_unrelated,
                reason = "pivot element was swapped to front"
            )]
            let Some(pivot) = partition.first() else {
                unreachable!("caller ensures there is at least one element");
            };

            if element < pivot {
                if let Some(incremented) = mid.checked_add(1) {
                    mid = incremented;
                } else {
                    unreachable!("at most the index of the last element");
                }

                partition.swap(current, mid);
            }
        }

        // Place the pivot element at that middle index.
        partition.swap(0, mid);

        // Split into those two partitions.
        let (left, right) = partition.split_at_mut(mid);

        // Ignore the pivot element since it is in sorted position.
        let Some((_pivot, right)) = right.split_first_mut() else {
            unreachable!("contains at least the pivot element");
        };

        (left, right)
    });
}

/// Sort `elements` via quick sort with a three-way partition scheme.
///
/// <div class="warning">
/// This is unstable so the order of equivalent elements is not guaranteed.
/// </div>
///
/// # Algorithm
/// Place an element (the pivot) and all elements equivalent to it into sorted
/// position by partitioning the elements on it, i.e., placing smaller elements
/// before it and larger elements after it. This implementation is
/// fundamentally the same as [`lomuto`], except it also keeps track of
/// elements equivalent to the pivot placing them into a third partition
/// between those smaller and those larger. The resulting non-equal partitions
/// can then be independently recursively sorted since all elements of the left
/// partition are less-than all elements within the right partition.
///
/// # Performance
/// This algorithm always consumes O(N) memory but has varying time
/// complexity depending on the input. The best-case occurs when the partition
/// evenly divides the input into two sub-slices containing the same number of
/// elements taking 𝛀(N ⋅ log N), the worst-case occurs when the partition
/// separates a single element from the rest taking O(N<sup>2</sup>), and the
/// average is 𝚯(N ⋅ log N) time.
///
/// # See Also
/// [Wikipedia](https://en.wikipedia.org/wiki/Dutch_national_flag_problem).
///
/// # Examples
/// ```
/// use rust::algorithm::sort::quick::three_way;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// three_way(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn three_way<T: Ord>(elements: &mut [T]) {
    recurse(elements, &|partition, mut pivot| {
        debug_assert!(pivot < partition.len(), "pivot must be within bounds");

        // The index range containing elements equal to the pivot.
        let mut equal = 0..partition.len();

        // The index of the element currently being placed into a partition.
        let mut current = 0;

        while current < equal.end {
            match partition.get(current).cmp(&partition.get(pivot)) {
                core::cmp::Ordering::Less => {
                    // Swap might move the pivot element.
                    #[expect(clippy::else_if_without_else, reason = "pivot is not swapped")]
                    if pivot == current {
                        pivot = equal.start;
                    } else if pivot == equal.start {
                        pivot = current;
                    }

                    partition.swap(current, equal.start);

                    _ = equal.next();

                    if let Some(incremented) = current.checked_add(1) {
                        current = incremented;
                    } else {
                        unreachable!("loop will exit so at most `usize::MAX`");
                    }
                }
                core::cmp::Ordering::Greater => {
                    _ = equal.next_back();

                    // Swap might move the pivot element.
                    #[expect(clippy::else_if_without_else, reason = "pivot is not swapped")]
                    if pivot == current {
                        pivot = equal.end;
                    } else if pivot == equal.end {
                        pivot = current;
                    }

                    partition.swap(current, equal.end);
                }
                core::cmp::Ordering::Equal => {
                    if let Some(incremented) = current.checked_add(1) {
                        current = incremented;
                    } else {
                        unreachable!("loop will exit so at most `usize::MAX`");
                    }
                }
            }
        }

        let (rest, greater) = partition.split_at_mut(equal.end);

        let (less, _equal) = rest.split_at_mut(equal.start);

        (less, greater)
    });
}

#[cfg(test)]
mod test {
    use super::*;

    mod hoare {
        use super::*;

        #[test]
        fn when_empty_then_does_nothing() {
            let mut elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            hoare(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn when_single_element_then_does_not_modify_it() {
            for element in 0..256 {
                let mut elements = [element];

                debug_assert_eq!(elements.len(), 1);

                hoare(&mut elements);

                assert_eq!(elements, [element]);
            }
        }

        #[test]
        fn when_all_elements_are_equivalent_then_does_not_modify_them() {
            for value in 0..256 {
                for length in 2..256 {
                    let mut elements: Vec<_> = core::iter::repeat_n(value, length).collect();

                    debug_assert!(elements.iter().all(|element| element == &value));

                    hoare(&mut elements);

                    assert!(elements.into_iter().all(|element| element == value));
                }
            }
        }

        #[test]
        fn when_already_sorted_then_maintains_order() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).collect();

                debug_assert!(elements.is_sorted());

                hoare(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_in_reverse_sorted_order_then_is_reversed() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.iter().rev().is_sorted());

                hoare(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_elements_are_repeated_then_they_are_grouped_together() {
            for repeat in 2..128 {
                let mut elements: Vec<_> = (0..256)
                    .map(|element| {
                        if element % repeat == 0 {
                            repeat
                        } else {
                            element
                        }
                    })
                    .collect();

                let count = elements.len().div_ceil(repeat);

                debug_assert_eq!(
                    elements
                        .iter()
                        .filter(|element| *element == &repeat)
                        .count(),
                    count
                );

                hoare(&mut elements);

                let index = elements
                    .iter()
                    .position(|element| element == &repeat)
                    .expect("first occurrence of repeated element");

                assert!(
                    elements[index..index + count]
                        .iter()
                        .all(|element| element == &repeat)
                );
            }
        }

        #[test]
        fn when_odd_number_of_elements_then_sorts_them() {
            for length in (1..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 != 0);

                hoare(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_even_number_of_elements_then_sorts_them() {
            for length in (0..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 == 0);

                hoare(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_chunks_are_sorted_then_sorts_them_into_rest() {
            for length in 2..255 {
                let mut elements: Vec<_> = (0..256).rev().collect();

                for chunk in elements.chunks_mut(length) {
                    chunk.reverse();

                    debug_assert!(chunk.is_sorted());
                }

                debug_assert!(!elements.is_sorted());

                hoare(&mut elements);

                assert!(elements.is_sorted());
            }
        }
    }

    mod lomuto {
        use super::*;

        #[test]
        fn when_empty_then_does_nothing() {
            let mut elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            lomuto(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn when_single_element_then_does_not_modify_it() {
            for element in 0..256 {
                let mut elements = [element];

                debug_assert_eq!(elements.len(), 1);

                lomuto(&mut elements);

                assert_eq!(elements, [element]);
            }
        }

        #[test]
        fn when_all_elements_are_equivalent_then_does_not_modify_them() {
            for value in 0..256 {
                for length in 2..256 {
                    let mut elements: Vec<_> = core::iter::repeat_n(value, length).collect();

                    debug_assert!(elements.iter().all(|element| element == &value));

                    lomuto(&mut elements);

                    assert!(elements.into_iter().all(|element| element == value));
                }
            }
        }

        #[test]
        fn when_already_sorted_then_maintains_order() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).collect();

                debug_assert!(elements.is_sorted());

                lomuto(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_in_reverse_sorted_order_then_is_reversed() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.iter().rev().is_sorted());

                lomuto(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_elements_are_repeated_then_they_are_grouped_together() {
            for repeat in 2..128 {
                let mut elements: Vec<_> = (0..256)
                    .map(|element| {
                        if element % repeat == 0 {
                            repeat
                        } else {
                            element
                        }
                    })
                    .collect();

                let count = elements.len().div_ceil(repeat);

                debug_assert_eq!(
                    elements
                        .iter()
                        .filter(|element| *element == &repeat)
                        .count(),
                    count
                );

                lomuto(&mut elements);

                let index = elements
                    .iter()
                    .position(|element| element == &repeat)
                    .expect("first occurrence of repeated element");

                assert!(
                    elements[index..index + count]
                        .iter()
                        .all(|element| element == &repeat)
                );
            }
        }

        #[test]
        fn when_odd_number_of_elements_then_sorts_them() {
            for length in (1..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 != 0);

                lomuto(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_even_number_of_elements_then_sorts_them() {
            for length in (0..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 == 0);

                lomuto(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_chunks_are_sorted_then_sorts_them_into_rest() {
            for length in 2..255 {
                let mut elements: Vec<_> = (0..256).rev().collect();

                for chunk in elements.chunks_mut(length) {
                    chunk.reverse();

                    debug_assert!(chunk.is_sorted());
                }

                debug_assert!(!elements.is_sorted());

                lomuto(&mut elements);

                assert!(elements.is_sorted());
            }
        }
    }

    mod three_way {
        use super::*;

        #[test]
        fn when_empty_then_does_nothing() {
            let mut elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            three_way(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn when_single_element_then_does_not_modify_it() {
            for element in 0..256 {
                let mut elements = [element];

                debug_assert_eq!(elements.len(), 1);

                three_way(&mut elements);

                assert_eq!(elements, [element]);
            }
        }

        #[test]
        fn when_all_elements_are_equivalent_then_does_not_modify_them() {
            for value in 0..256 {
                for length in 2..256 {
                    let mut elements: Vec<_> = core::iter::repeat_n(value, length).collect();

                    debug_assert!(elements.iter().all(|element| element == &value));

                    three_way(&mut elements);

                    assert!(elements.into_iter().all(|element| element == value));
                }
            }
        }

        #[test]
        fn when_already_sorted_then_maintains_order() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).collect();

                debug_assert!(elements.is_sorted());

                three_way(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_in_reverse_sorted_order_then_is_reversed() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.iter().rev().is_sorted());

                three_way(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_elements_are_repeated_then_they_are_grouped_together() {
            for repeat in 2..128 {
                let mut elements: Vec<_> = (0..256)
                    .map(|element| {
                        if element % repeat == 0 {
                            repeat
                        } else {
                            element
                        }
                    })
                    .collect();

                let count = elements.len().div_ceil(repeat);

                debug_assert_eq!(
                    elements
                        .iter()
                        .filter(|element| *element == &repeat)
                        .count(),
                    count
                );

                three_way(&mut elements);

                let index = elements
                    .iter()
                    .position(|element| element == &repeat)
                    .expect("first occurrence of repeated element");

                assert!(
                    elements[index..index + count]
                        .iter()
                        .all(|element| element == &repeat)
                );
            }
        }

        #[test]
        fn when_odd_number_of_elements_then_sorts_them() {
            for length in (1..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 != 0);

                three_way(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_even_number_of_elements_then_sorts_them() {
            for length in (0..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 == 0);

                three_way(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_chunks_are_sorted_then_sorts_them_into_rest() {
            for length in 2..255 {
                let mut elements: Vec<_> = (0..256).rev().collect();

                for chunk in elements.chunks_mut(length) {
                    chunk.reverse();

                    debug_assert!(chunk.is_sorted());
                }

                debug_assert!(!elements.is_sorted());

                three_way(&mut elements);

                assert!(elements.is_sorted());
            }
        }
    }
}
