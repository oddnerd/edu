//! Implementations of [Bubble Sort](https://en.wikipedia.org/wiki/Bubble_sort).

/// Sort `elements` using naive bubble sort.
///
/// Iteratively 'bubble up' the largest yet to be sorted element by iterating
/// adjacent pairs from the start of the list and swapping the largest element
/// to the end until in sorted position.
///
/// # Performance
/// This method takes O(N<sup>2</sup>) time and consumes O(1) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::bubble::naive;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// naive(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn naive<T: Ord>(elements: &mut [T]) {
    for sorted_position in (0..elements.len()).rev() {
        for current_index in 0..sorted_position {
            let Some(next_index) = current_index.checked_add(1) else {
                unreachable!("loops ensure `current index <= usize::MAX - 1`");
            };

            let (Some(current_element), Some(next_element)) =
                (elements.get(current_index), elements.get(next_index))
            else {
                unreachable!("loops ensure both indexes are within bounds");
            };

            if current_element > next_element {
                elements.swap(current_index, next_index);
            }
        }
    }
}

/// Sort `elements` using optimized bubble sort.
///
/// Fundamentally the same as the [`naive`] implementation, but takes advantage
/// of the fact that if no swap occurs past some index, then the elements
/// after that index were proven to be sorted by that iteration hence they do
/// not need to be compared against in future iteration.
///
/// # Performance
/// This method takes O(N<sup>2</sup>) time and consumes O(1) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::bubble::optimized;
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

        for current_index in 1..remaining {
            let Some(previous_index) = current_index.checked_sub(1) else {
                unreachable!("inner loop ensures current_index >= 1");
            };

            let (Some(current_element), Some(previous_element)) =
                (elements.get(current_index), elements.get(previous_index))
            else {
                unreachable!("outer loop ensures both indexes are in bounds");
            };

            if previous_element > current_element {
                elements.swap(previous_index, current_index);

                last_swap = current_index;
            }
        }

        // No swaps occurred past this index => those elements are sorted.
        remaining = last_swap;
    }
}

/// Sort `elements` using bidirectional (cocktail shaker) bubble sort.
///
/// The [`optimized`] solution moves larger elements to the end of the list
/// faster than it can move smaller elements to the front because larger
/// elements are successively swapped per each iteration of the inner loop
/// whereas smaller elements can only move down per each iteration of the outer
/// loop. In contrast, this implementation merely repeats the inner loop in the
/// opposite direction thereby efficiently moving the largest element to the
/// end of the list and the smallest to the beginning for each iteration of the
/// outer loop.
///
/// # Performance
/// This method takes O(N<sup>2</sup>) time and consumes O(1) memory.
///
/// # See Also
/// [Wikipedia](https://en.wikipedia.org/wiki/Cocktail_shaker_sort).
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::bubble::bidirectional;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// bidirectional(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn bidirectional<T: Ord>(elements: &mut [T]) {
    let mut remaining = 1..elements.len();

    while !remaining.is_empty() {
        let mut last_swap = 0;
        for current_index in remaining.clone() {
            let Some(previous_index) = current_index.checked_sub(1) else {
                unreachable!("loop ensures `current_index >= 1`");
            };

            let (Some(current_element), Some(previous_element)) =
                (elements.get(current_index), elements.get(previous_index))
            else {
                unreachable!("loop ensures both indexes are within bounds");
            };

            if previous_element > current_element {
                elements.swap(previous_index, current_index);

                last_swap = current_index;
            }
        }
        remaining = remaining.start..last_swap;

        last_swap = elements.len();
        for current_index in remaining.clone().rev() {
            let Some(previous_index) = current_index.checked_sub(1) else {
                unreachable!("loop ensures `current_index >= 1`");
            };

            let (Some(current_element), Some(previous_element)) =
                (elements.get(current_index), elements.get(previous_index))
            else {
                unreachable!("loop ensures both indexes are within bounds");
            };

            if previous_element > current_element {
                elements.swap(previous_index, current_index);

                last_swap = current_index;
            }
        }
        remaining = last_swap..remaining.end;
    }
}

/// Sort `elements` using parallel (odd-even) bubble sort.
///
/// Fundamentally the same as [`naive`], except this variation is trivially
/// modified to execute asynchronously. Instead of the inner loop iterating
/// over overlapping windows of two elements, this variation iterates over
/// non-overlapping chunks of two elements
///
/// # Performance
/// This method takes O(N<sup>2</sup>) time and consumes O(1) memory.
///
/// # See Also
/// [Wikipedia](https://en.wikipedia.org/wiki/Odd%E2%80%93even_sort).
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::bubble::parallel;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// parallel(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn parallel<T: Ord>(elements: &mut [T]) {
    let mut sorted = false;

    while !sorted {
        sorted = true;

        // Sort pairs of elements starting from an even index.
        // Each iteration of this loop can be executed in parallel.
        for pair in elements.chunks_exact_mut(2) {
            let Some((first, remaining)) = pair.split_first_mut() else {
                unreachable!("chunks exact => pair has exactly two elements");
            };

            let Some((last, _)) = remaining.split_last_mut() else {
                unreachable!("chunks exact => pair has exactly two elements");
            };

            if first > last {
                core::mem::swap(first, last);
                sorted = false;
            }
        }

        // Ignoring the first element offsets the pairs by one.
        let Some((_, elements)) = elements.split_first_mut() else {
            debug_assert!(elements.len() < 2, "only condition its none");
            return;
        };

        // Sort pairs of elements starting from an odd index.
        // Each iteration of this loop can be executed in parallel.
        for pair in elements.chunks_exact_mut(2) {
            let Some((first, remaining)) = pair.split_first_mut() else {
                unreachable!("chunks exact => pair has exactly two elements");
            };

            let Some((last, _)) = remaining.split_last_mut() else {
                unreachable!("chunks exact => pair has exactly two elements");
            };

            if first > last {
                core::mem::swap(first, last);
                sorted = false;
            }
        }
    }
}

/// Sort `elements` using parallel (odd-even) bubble sort.
///
/// Fundamentally the same as [`naive`], except instead of comparing directly
/// adjacent elements, this variation compares elements separated by some
/// decreasing gap thereby allowing elements to move large distances with only
/// a single swap. This effectively does to bubble sort what the [`shell`]
/// variation does to insertion sort.
///
/// # Performance
/// This method takes O(N<sup>2</sup>) time and consumes O(1) memory.
///
/// # See Also
/// [Wikipedia](https://en.wikipedia.org/wiki/Comb_sort).
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::bubble::comb;
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
            sorted = true;
        }

        for current_index in gap..elements.len() {
            let Some(gap_index) = current_index.checked_sub(gap) else {
                unreachable!("loop ensures `current_index >= gap`");
            };

            let (Some(current_element), Some(gap_element)) =
                (elements.get(current_index), elements.get(gap_index))
            else {
                unreachable!("loop ensures both indexes are within bounds");
            };

            if gap_element > current_element {
                elements.swap(gap_index, current_index);

                sorted = false;
            }
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

    mod naive {
        use super::*;

        #[test]
        fn empty() {
            let mut elements = [usize::default(); 0];

            naive(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            naive(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            naive(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            naive(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            naive(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            naive(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod optimized {
        use super::*;

        #[test]
        fn empty() {
            let mut elements = [usize::default(); 0];

            optimized(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            optimized(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            optimized(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            optimized(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            optimized(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            optimized(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod bidirectional {
        use super::*;

        #[test]
        fn empty() {
            let mut elements = [usize::default(); 0];

            bidirectional(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            bidirectional(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            bidirectional(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            bidirectional(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            bidirectional(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            bidirectional(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod parallel {
        use super::*;

        #[test]
        fn empty() {
            let mut elements = [usize::default(); 0];

            parallel(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            parallel(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            parallel(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            parallel(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            parallel(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            parallel(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod comb {
        use super::*;

        #[test]
        fn empty() {
            let mut elements = [usize::default(); 0];

            comb(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            comb(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            comb(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            comb(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            comb(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            comb(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }
}
