//! Implementations of [Bubble Sort](https://en.wikipedia.org/wiki/Bubble_sort).

/// Sort `elements` via naive bubble sort.
///
/// # Algorithm
/// Iterate through overlapping pairs of elements, swapping them if necessary
/// such that the element with the largest value will be contained in the
/// (theoretical) overlapping pair of elements in the next iteration. The
/// element with overall largest value has now 'bubbled up' into sorted
/// position and can be split from the remaining unsorted elements with smaller
/// values. The process is repeated for each index finding the element with the
/// next overall largest value until all elements are sorted.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(N<sup>2</sup>) | 𝛀(N<sup>2</sup>) | 𝚯(N<sup>2</sup>) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
///
/// # Examples
/// ```
/// use rust::algorithm::sort::bubble::naive;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// naive(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn naive<T: Ord>(elements: &mut [T]) {
    for sorted_position in (0..elements.len()).rev() {
        for current in 0..sorted_position {
            let Some(next) = current.checked_add(1) else {
                unreachable!("loops ensure `current index <= usize::MAX - 1`");
            };

            if elements.get(current) > elements.get(next) {
                elements.swap(current, next);
            }
        }
    }
}

/// Sort `elements` via optimized bubble sort.
///
/// # Algorithm
/// Ostensibly the same as the [`naive`] implementation, however this has an
/// optimization whereby if no swap occurs past some index, then that portion
/// of the input is naturally sorted and can be skipped in future iterations.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(N<sup>2</sup>) | 𝛀(N) | 𝚯(N<sup>2</sup>) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
///
/// # Examples
/// ```
/// use rust::algorithm::sort::bubble::optimized;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// optimized(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn optimized<T: Ord>(elements: &mut [T]) {
    let mut remaining = elements.len();

    while remaining > 1 {
        let mut last_swap = 0;

        for current in 1..remaining {
            let Some(previous) = current.checked_sub(1) else {
                unreachable!("inner loop ensures `current_index >= 1`");
            };

            if elements.get(previous) > elements.get(current) {
                elements.swap(previous, current);

                last_swap = current;
            }
        }

        // No swaps occurred past this index => those elements are sorted.
        remaining = last_swap;
    }
}

/// Sort `elements` via bidirectional (cocktail shaker) bubble sort.
///
/// # Algorithm
/// Ostensibly the same as the [`optimized`] implementation, however the
/// overlapping pairs of elements are iterated in alternating directions.
///
/// Observe that the [`optimized`] implementation can move elements with large
/// values multiple positions by repeated swaps, but elements with small values
/// are only moved at most one position since it will not be contained in the
/// overlapping pair of elements in the next iteration(s). In contrast, this
/// implementation alternates between finding the element with the largest
/// value and finding the element with smallest value, thereby having different
/// performance characteristics.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(N<sup>2</sup>) | 𝛀(N) | 𝚯(N<sup>2</sup>) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
///
/// # See Also
/// [Wikipedia](https://en.wikipedia.org/wiki/Cocktail_shaker_sort).
///
/// # Examples
/// ```
/// use rust::algorithm::sort::bubble::bidirectional;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// bidirectional(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn bidirectional<T: Ord>(elements: &mut [T]) {
    let mut unsorted = 1..elements.len();

    // Flag to signify left versus right direction of iteration.
    let mut rightward = true;

    while !unsorted.is_empty() {
        let mut last_swap = if rightward { 0 } else { elements.len() };

        let bubble = |current: usize| {
            let Some(previous) = current.checked_sub(1) else {
                unreachable!("loop ensures `current_index >= 1`");
            };

            if elements.get(previous) > elements.get(current) {
                elements.swap(previous, current);

                last_swap = current;
            }
        };

        if rightward {
            unsorted.clone().for_each(bubble);

            unsorted = unsorted.start..last_swap;
        } else {
            unsorted.clone().rev().for_each(bubble);

            unsorted = last_swap..unsorted.end;
        };

        rightward = !rightward;
    }
}

/// Sort `elements` via parallel (odd-even) bubble sort.
///
/// # Algorithm
/// Iterate through non-overlapping pairs of elements, swapping them if
/// necessary such that the element with the largest value is in the position
/// with the larger of the two indexes. Repeat whilst alternating if elements
/// are paired with the left or right neighbour thereby allowing elements with
/// larger values to 'bubble up' multiple positions into sorted order via
/// repeated swaps. Once two consecutive iterations occur without swapping any
/// elements, therefore all overlapping pairs of elements are sorted, hence the
/// entirety of the input has been sorted.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(N<sup>2</sup>) | 𝛀(N) | 𝚯(N<sup>2</sup>) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
///
/// # See Also
/// [Wikipedia](https://en.wikipedia.org/wiki/Odd%E2%80%93even_sort).
///
/// # Examples
/// ```
/// use rust::algorithm::sort::bubble::parallel;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// parallel(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn parallel<T: Ord>(elements: &mut [T]) {
    // The entire input is sorted only if consecutive loops invoke no swaps.
    let mut even_pairs_sorted = false;
    let mut odd_pairs_sorted = false;

    // Flag to signify if pairs should be offset.
    let mut offset = false;

    while !(even_pairs_sorted && odd_pairs_sorted) {
        // Only on the second  Assume no swaps are necessary.
        if offset {
            odd_pairs_sorted = true;
        } else {
            even_pairs_sorted = true;
        }

        let Some(elements) = elements.get_mut(usize::from(offset)..) else {
            debug_assert_eq!(elements.len(), 0, "only condition it is none");

            return;
        };

        // Each iteration of this loop can be executed in parallel.
        for pair in elements.chunks_exact_mut(2) {
            if pair.first() > pair.last() {
                pair.swap(0, 1);

                // A swap was necessary, so more might be too.
                if offset {
                    odd_pairs_sorted = false;
                } else {
                    even_pairs_sorted = false;
                }
            }
        }

        offset = !offset;
    }
}

/// Sort `elements` via comb bubble sort.
///
/// # Algorithm
/// Fundamentally the same as [`parallel`], except instead of comparing
/// directly adjacent elements, this variation compares elements separated by
/// some decreasing gap thereby allowing elements to move large distances with
/// only a single swap. This effectively does to bubble sort what the
/// [`super::insertion::shell`] variation does to insertion sort.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(N<sup>2</sup>) | 𝛀(N ⋅ log N) | 𝚯(N<sup>2</sup>) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
///
/// # See Also
/// [Wikipedia](https://en.wikipedia.org/wiki/Comb_sort).
///
/// # Examples
/// ```
/// use rust::algorithm::sort::bubble::comb;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// comb(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn comb<T: Ord>(elements: &mut [T]) {
    let mut gap = elements.len();

    let mut sorted = false;

    while !sorted {
        gap /= 2;

        if gap <= 1 {
            gap = 1;

            // This is the base case, so assume no swaps are necessary.
            sorted = true;
        }

        for current in gap..elements.len() {
            let Some(other) = current.checked_sub(gap) else {
                unreachable!("loop ensures `current_index >= gap`");
            };

            if elements.get(other) > elements.get(current) {
                elements.swap(other, current);

                // A swap was necessary, so more might be too.
                sorted = false;
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    mod naive {
        use super::*;

        #[test]
        fn when_empty_then_does_nothing() {
            let mut elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            naive(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn when_single_element_then_does_not_modify_it() {
            for element in 0..256 {
                let mut elements = [element];

                debug_assert_eq!(elements.len(), 1);

                naive(&mut elements);

                assert_eq!(elements, [element]);
            }
        }

        #[test]
        fn when_all_elements_are_equivalent_then_does_not_modify_them() {
            for value in 0..256 {
                for length in 2..256 {
                    let mut elements: Vec<_> = core::iter::repeat_n(value, length).collect();

                    debug_assert!(elements.iter().all(|element| element == &value));

                    naive(&mut elements);

                    assert!(elements.into_iter().all(|element| element == value));
                }
            }
        }

        #[test]
        fn when_already_sorted_then_maintains_order() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).collect();

                debug_assert!(elements.is_sorted());

                naive(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_in_reverse_sorted_order_then_is_reversed() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.iter().rev().is_sorted());

                naive(&mut elements);

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

                naive(&mut elements);

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

                naive(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_even_number_of_elements_then_sorts_them() {
            for length in (0..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 == 0);

                naive(&mut elements);

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

                naive(&mut elements);

                assert!(elements.is_sorted());
            }
        }
    }

    mod optimized {
        use super::*;

        #[test]
        fn when_empty_then_does_nothing() {
            let mut elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            optimized(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn when_single_element_then_does_not_modify_it() {
            for element in 0..256 {
                let mut elements = [element];

                debug_assert_eq!(elements.len(), 1);

                optimized(&mut elements);

                assert_eq!(elements, [element]);
            }
        }

        #[test]
        fn when_all_elements_are_equivalent_then_does_not_modify_them() {
            for value in 0..256 {
                for length in 2..256 {
                    let mut elements: Vec<_> = core::iter::repeat_n(value, length).collect();

                    debug_assert!(elements.iter().all(|element| element == &value));

                    optimized(&mut elements);

                    assert!(elements.into_iter().all(|element| element == value));
                }
            }
        }

        #[test]
        fn when_already_sorted_then_maintains_order() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).collect();

                debug_assert!(elements.is_sorted());

                optimized(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_in_reverse_sorted_order_then_is_reversed() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.iter().rev().is_sorted());

                optimized(&mut elements);

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

                optimized(&mut elements);

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

                optimized(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_even_number_of_elements_then_sorts_them() {
            for length in (0..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 == 0);

                optimized(&mut elements);

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

                naive(&mut elements);

                assert!(elements.is_sorted());
            }
        }
    }

    mod bidirectional {
        use super::*;

        #[test]
        fn when_empty_then_does_nothing() {
            let mut elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            bidirectional(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn when_single_element_then_does_not_modify_it() {
            for element in 0..256 {
                let mut elements = [element];

                debug_assert_eq!(elements.len(), 1);

                bidirectional(&mut elements);

                assert_eq!(elements, [element]);
            }
        }

        #[test]
        fn when_all_elements_are_equivalent_then_does_not_modify_them() {
            for value in 0..256 {
                for length in 2..256 {
                    let mut elements: Vec<_> = core::iter::repeat_n(value, length).collect();

                    debug_assert!(elements.iter().all(|element| element == &value));

                    bidirectional(&mut elements);

                    assert!(elements.into_iter().all(|element| element == value));
                }
            }
        }

        #[test]
        fn when_already_sorted_then_maintains_order() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).collect();

                debug_assert!(elements.is_sorted());

                bidirectional(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_in_reverse_sorted_order_then_is_reversed() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.iter().rev().is_sorted());

                bidirectional(&mut elements);

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

                bidirectional(&mut elements);

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

                bidirectional(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_even_number_of_elements_then_sorts_them() {
            for length in (0..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 == 0);

                bidirectional(&mut elements);

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

                naive(&mut elements);

                assert!(elements.is_sorted());
            }
        }
    }

    mod parallel {
        use super::*;

        #[test]
        fn when_empty_then_does_nothing() {
            let mut elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            parallel(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn when_single_element_then_does_not_modify_it() {
            for element in 0..256 {
                let mut elements = [element];

                debug_assert_eq!(elements.len(), 1);

                parallel(&mut elements);

                assert_eq!(elements, [element]);
            }
        }

        #[test]
        fn when_all_elements_are_equivalent_then_does_not_modify_them() {
            for value in 0..256 {
                for length in 2..256 {
                    let mut elements: Vec<_> = core::iter::repeat_n(value, length).collect();

                    debug_assert!(elements.iter().all(|element| element == &value));

                    parallel(&mut elements);

                    assert!(elements.into_iter().all(|element| element == value));
                }
            }
        }

        #[test]
        fn when_already_sorted_then_maintains_order() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).collect();

                debug_assert!(elements.is_sorted());

                parallel(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_in_reverse_sorted_order_then_is_reversed() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.iter().rev().is_sorted());

                parallel(&mut elements);

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

                parallel(&mut elements);

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

                parallel(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_even_number_of_elements_then_sorts_them() {
            for length in (0..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 == 0);

                parallel(&mut elements);

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

                parallel(&mut elements);

                assert!(elements.is_sorted());
            }
        }
    }

    mod comb {
        use super::*;

        #[test]
        fn when_empty_then_does_nothing() {
            let mut elements: [usize; 0] = [];

            debug_assert!(elements.is_empty());

            comb(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn when_single_element_then_does_not_modify_it() {
            for element in 0..256 {
                let mut elements = [element];

                debug_assert_eq!(elements.len(), 1);

                comb(&mut elements);

                assert_eq!(elements, [element]);
            }
        }

        #[test]
        fn when_all_elements_are_equivalent_then_does_not_modify_them() {
            for value in 0..256 {
                for length in 2..256 {
                    let mut elements: Vec<_> = core::iter::repeat_n(value, length).collect();

                    debug_assert!(elements.iter().all(|element| element == &value));

                    comb(&mut elements);

                    assert!(elements.into_iter().all(|element| element == value));
                }
            }
        }

        #[test]
        fn when_already_sorted_then_maintains_order() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).collect();

                debug_assert!(elements.is_sorted());

                comb(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_in_reverse_sorted_order_then_is_reversed() {
            for length in 2..256 {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.iter().rev().is_sorted());

                comb(&mut elements);

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

                comb(&mut elements);

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

                comb(&mut elements);

                assert!(elements.is_sorted());
            }
        }

        #[test]
        fn when_even_number_of_elements_then_sorts_them() {
            for length in (0..256).step_by(2) {
                let mut elements: Vec<_> = (0..length).rev().collect();

                debug_assert!(elements.len() % 2 == 0);

                comb(&mut elements);

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

                comb(&mut elements);

                assert!(elements.is_sorted());
            }
        }
    }
}
