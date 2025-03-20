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

    // Flag to signify left versus right direction of iteration.
    let mut rightward = true;

    while !unsorted.is_empty() {
        let mut last_swap = if rightward {
            0
        } else {
            elements.len()
        };

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
/// # Methodology
/// Iterate through non-overlapping pairs of elements swapping the largest so
/// it is closest to the end. Note that because each pair is independent, they
/// can be compared in parallel. Repeat whilst alternating if elements are
/// paired with their right or left neighbour until no swaps are necessary.
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
    let mut sorted = false;

    // Flag to signify if pairs should be offset.
    let mut offset = false;

    while !sorted {
        // Assume no swaps are necessary.
        sorted = true;

        let Some(elements) = elements.get_mut(usize::from(offset)..) else {
            debug_assert_eq!(elements.len(), 0, "only condition it is none");

            return;
        };

        // Each iteration of this loop can be executed in parallel.
        for pair in elements.chunks_exact_mut(2) {
            if pair.first() > pair.last() {
                pair.swap(0, 1);

                // A swap was necessary, so more might be too.
                sorted = false;
            }
        }

        offset = !offset;
    }
}

/// Sort `elements` via comb bubble sort.
///
/// # Methodology
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
        fn handles_when_input_is_empty() {
            let mut elements: [usize; 0] = [];

            bidirectional(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn handles_when_input_is_single_element() {
            let mut elements = [0];

            bidirectional(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn does_not_modify_input_when_already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            debug_assert!(elements.is_sorted());

            bidirectional(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn will_swap_elements_if_in_decreasing_order() {
            let mut elements = [1, 0];

            bidirectional(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_odd_length() {
            let mut elements = [2, 1, 0];

            bidirectional(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_even_length() {
            let mut elements = [2, 0, 3, 1];

            bidirectional(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod parallel {
        use super::*;

        #[test]
        fn handles_when_input_is_empty() {
            let mut elements: [usize; 0] = [];

            parallel(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn handles_when_input_is_single_element() {
            let mut elements = [0];

            parallel(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn does_not_modify_input_when_already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            debug_assert!(elements.is_sorted());

            parallel(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn will_swap_elements_if_in_decreasing_order() {
            let mut elements = [1, 0];

            parallel(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_odd_length() {
            let mut elements = [2, 1, 0];

            parallel(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_even_length() {
            let mut elements = [2, 0, 3, 1];

            parallel(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod comb {
        use super::*;

        #[test]
        fn handles_when_input_is_empty() {
            let mut elements: [usize; 0] = [];

            comb(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn handles_when_input_is_single_element() {
            let mut elements = [0];

            comb(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn does_not_modify_input_when_already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            debug_assert!(elements.is_sorted());

            comb(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn will_swap_elements_if_in_decreasing_order() {
            let mut elements = [1, 0];

            comb(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_odd_length() {
            let mut elements = [2, 1, 0];

            comb(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_even_length() {
            let mut elements = [2, 0, 3, 1];

            comb(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }
}
