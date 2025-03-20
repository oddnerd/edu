//! Implementations of [Bubble Sort](https://en.wikipedia.org/wiki/Bubble_sort).

/// Sort `elements` via naive bubble sort.
///
/// # Methodology
/// Iterate through overlapping pairs of elements swapping the largest so it is
/// closer to the end until the largest element has 'bubbled up' to the end
/// of the unsorted elements. The element is now in sorted position so it can
/// be discarded and the process repeated until all elements are sorted.
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
/// # Methodology
/// Fundamentally the same as the [`naive`] implementation, however the index
/// of the most recent swap is saved. For each iteration, the elements after
/// that index must be in sorted order so they can be discarded from the input.
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
/// # Methodology
/// Observe that because the [`optimized`] implementation iterates from the
/// left of the input to the right, larger elements can move multiple positions
/// towards their sorted position whereas smaller elements can only ever move
/// one position towards theirs. In contrast, this implementation alternates
/// iteration direction thereby having different performance characteristics.
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

    while !unsorted.is_empty() {
        let mut last_swap = 0;
        for current in unsorted.clone() {
            let Some(previous) = current.checked_sub(1) else {
                unreachable!("loop ensures `current_index >= 1`");
            };

            if elements.get(previous) > elements.get(current) {
                elements.swap(previous, current);

                last_swap = current;
            }
        }
        unsorted = unsorted.start..last_swap;

        last_swap = elements.len();
        for current in unsorted.clone().rev() {
            let Some(previous) = current.checked_sub(1) else {
                unreachable!("loop ensures `current_index >= 1`");
            };

            if elements.get(previous) > elements.get(current) {
                elements.swap(previous, current);

                last_swap = current;
            }
        }
        unsorted = last_swap..unsorted.end;
    }
}

/// Sort `elements` via parallel (odd-even) bubble sort.
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
/// use rust::algorithm::sort::bubble::parallel;
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
            debug_assert!(elements.is_empty(), "only condition it is none");
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

/// Sort `elements` via comb bubble sort.
///
/// Fundamentally the same as [`naive`], except instead of comparing directly
/// adjacent elements, this variation compares elements separated by some
/// decreasing gap thereby allowing elements to move large distances with only
/// a single swap. This effectively does to bubble sort what the
/// [`super::insertion::shell`] variation does to insertion sort.
///
/// # Performance
/// This method takes O(N<sup>2</sup>) time and consumes O(1) memory.
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
mod test {
    use super::*;

    mod naive {
        use super::*;

        #[test]
        fn handles_when_input_is_empty() {
            let mut elements: [usize; 0] = [];

            naive(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn handles_when_input_is_single_element() {
            let mut elements = [0];

            naive(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn does_not_modify_input_when_already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            debug_assert!(elements.is_sorted());

            naive(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn will_swap_elements_if_in_decreasing_order() {
            let mut elements = [1, 0];

            naive(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_odd_length() {
            let mut elements = [2, 1, 0];

            naive(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_even_length() {
            let mut elements = [2, 0, 3, 1];

            naive(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod optimized {
        use super::*;

        #[test]
        fn handles_when_input_is_empty() {
            let mut elements: [usize; 0] = [];

            optimized(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn handles_when_input_is_single_element() {
            let mut elements = [0];

            optimized(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn does_not_modify_input_when_already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            debug_assert!(elements.is_sorted());

            optimized(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn will_swap_elements_if_in_decreasing_order() {
            let mut elements = [1, 0];

            optimized(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_odd_length() {
            let mut elements = [2, 1, 0];

            optimized(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_even_length() {
            let mut elements = [2, 0, 3, 1];

            optimized(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod bidirectional {
        use super::*;

        #[test]
        fn empty() {
            let mut elements: [usize; 0] = [];

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
            let mut elements: [usize; 0] = [];

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
            let mut elements: [usize; 0] = [];

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
