//! Implementations of [Insertion Sort](https://en.wikipedia.org/wiki/Insertion_sort).

/// Sort `elements` via iterative insertion sort.
///
/// # Algorithm
/// Starting from the first element of the slice which in isolation is a sorted
/// subsection, iteratively move the element to the right of the sorted
/// section to the left into sorted position within the sorted section
/// until all elements have been moved into that sorted section.
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
/// use rust::algorithm::sort::insertion::iterative;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// iterative(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn iterative<T: Ord>(elements: &mut [T]) {
    for sorted_length in 2..=elements.len() {
        // The sub-slice is sorted, except for the last element.
        let (sorted, _) = elements.split_at_mut(sorted_length);

        // Move the last element down the list until sorted.
        for current in (1..sorted.len()).rev() {
            let Some(previous) = current.checked_sub(1) else {
                unreachable!("loop stops at index 1, so never zero");
            };

            if sorted.get(previous) > sorted.get(current) {
                sorted.swap(current, previous);
            } else {
                break;
            }
        }
    }
}

/// Sort `elements` via recursive insertion sort.
///
/// # Algorithm
/// Recursively sort all but the last element, then move the last element
/// to the left into sorted position within the sorted section.
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
/// | O(N) | 𝛀(N) | 𝚯(N) |
///
/// # Examples
/// ```
/// use rust::algorithm::sort::insertion::recursive;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// recursive(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn recursive<T: Ord>(elements: &mut [T]) {
    let Some((_last, remaining)) = elements.split_last_mut() else {
        debug_assert!(elements.is_empty(), "only condition it is none");

        return;
    };

    // Sort everything except the last element.
    recursive(remaining);

    // Move the last element down the list until sorted.
    for current in (1..elements.len()).rev() {
        let Some(previous) = current.checked_sub(1) else {
            unreachable!("loop stops at index 1, so never zero");
        };

        if elements.get(previous) > elements.get(current) {
            elements.swap(current, previous);
        } else {
            break;
        }
    }
}

/// Sort `elements` via binary insertion sort.
///
/// <div class="warning">
/// This is unstable so the order of equivalent elements is not guaranteed.
/// </div>
///
/// # Algorithm
/// Similar to [`iterative`] except binary search is used to locate the index
/// within the already sorted section the next unsorted element should go,
/// thereby making fewer comparisons.
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
/// # Examples
/// ```
/// use rust::algorithm::sort::insertion::binary;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// binary(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn binary<T: Ord>(elements: &mut [T]) {
    for current in 1..elements.len() {
        let (sorted, unsorted) = elements.split_at(current);

        // The next element to be sorted.
        let Some(unsorted) = unsorted.first() else {
            unreachable!("loop ensures there will be at least one element");
        };

        // The index within the sorted section to place that element.
        let sorted = match sorted.binary_search(unsorted) {
            Ok(index) | Err(index) => index,
        };

        // The elements between that index and the element being sorted.
        let Some(to_rotate) = elements.get_mut(sorted..=current) else {
            unreachable!("both indexes in bound hence the range is in bound");
        };

        // Place that element into position by shifting elements in between.
        to_rotate.rotate_right(1);
    }
}

/// Sort `elements` via gnome insertion sort.
///
/// # Algorithm
/// Similar to [`iterative`] except the index is manually manipulated instead
/// of utilizing for loops.
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
/// [Wikipedia](https://en.wikipedia.org/wiki/Gnome_sort).
///
/// # Examples
/// ```
/// use rust::algorithm::sort::insertion::gnome;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// gnome(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn gnome<T: Ord>(elements: &mut [T]) {
    let mut index: usize = 1;

    while index < elements.len() {
        #[expect(
            clippy::arithmetic_side_effects,
            reason = "short-circuiting ensures `index > 0`"
        )]
        if index == 0 || elements.get(index - 1) <= elements.get(index) {
            if let Some(incremented) = index.checked_add(1) {
                index = incremented;
            } else {
                debug_assert_eq!(
                    elements.len(),
                    usize::MAX,
                    "only condition branch is invoked"
                );

                // This implies all elements have been sorted.
                break;
            }
        } else {
            let Some(decremented) = index.checked_sub(1) else {
                unreachable!("enclosing if ensures `index > 0`");
            };

            elements.swap(index, decremented);
            index = decremented;
        }
    }
}

/// Sort `elements` via shell insertion sort.
///
/// # Algorithm
/// This variation sorts elements separated by some gap such that starting from
/// some index, every element at an index offset by a multiple of the gap is in
/// sorted order. This results in the entire list being gap many interleaved
/// sorted sublists. The benefit of this variation is out-of-order elements are
/// only compared to and swapped with elements within the gap sublist thereby
/// moving large distances across the overall list without interacting with
/// absolutely every element before it. The gap is decreased to move elements
/// smaller distances for each iteration thereby moving it closer to overall
/// sorted order until a gap of one is reached which is the same as the
/// [`iterative`] solution, but by that iteration elements will only need
/// to be swapped with those directly adjacent.
///
/// The exact runtime performance of this variation depends greatly on the
/// specific gaps used. This implementation uses Hibbard's proposal which is
/// known to be suboptimal compared to Pratt's, but is still better than
/// Shell's original and does not excessively clutter the core algorithm with
/// constructing a complex gap sequence.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(N<sup>3/2</sup>) | 𝛀(N ⋅ log N) | 𝚯(N<sup>5/4</sup>)[^1] |
///
/// [^1]: Generally accepted conjecture based on experiment.
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
///
/// # See Also
/// [Wikipedia](https://en.wikipedia.org/wiki/Shellsort).
///
/// # Examples
/// ```
/// use rust::algorithm::sort::insertion::shell;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// shell(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn shell<T: Ord>(elements: &mut [T]) {
    let Some(log) = elements.len().checked_ilog2() else {
        debug_assert!(elements.is_empty(), "only condition it is none");

        return;
    };

    for exponent in (1..=log).rev() {
        let Some(gap) = usize::checked_pow(2, exponent) else {
            unreachable!("length of elements fits in `usize` so this will too");
        };

        let Some(gap) = gap.checked_sub(1) else {
            unreachable!("loop ensures `gap >= 2`");
        };

        for end in gap..elements.len() {
            for current in (gap..=end).rev().step_by(gap) {
                let Some(previous) = current.checked_sub(gap) else {
                    unreachable!("inner loop ensures `j >= gap` => `j >= 1`");
                };

                if elements.get(current) >= elements.get(previous) {
                    break;
                }

                elements.swap(current, previous);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    mod iterative {
        use super::*;

        #[test]
        fn handles_when_input_is_empty() {
            let mut elements: [usize; 0] = [];

            iterative(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn handles_when_input_is_single_element() {
            let mut elements = [0];

            iterative(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn does_not_modify_input_when_already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            debug_assert!(elements.is_sorted());

            iterative(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn will_swap_elements_if_in_decreasing_order() {
            let mut elements = [1, 0];

            iterative(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_odd_length() {
            let mut elements = [2, 1, 0];

            iterative(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_even_length() {
            let mut elements = [2, 0, 3, 1];

            iterative(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod recursive {
        use super::*;

        #[test]
        fn handles_when_input_is_empty() {
            let mut elements: [usize; 0] = [];

            recursive(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn handles_when_input_is_single_element() {
            let mut elements = [0];

            recursive(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn does_not_modify_input_when_already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            debug_assert!(elements.is_sorted());

            recursive(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn will_swap_elements_if_in_decreasing_order() {
            let mut elements = [1, 0];

            recursive(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_odd_length() {
            let mut elements = [2, 1, 0];

            recursive(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_even_length() {
            let mut elements = [2, 0, 3, 1];

            recursive(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod binary {
        use super::*;

        #[test]
        fn handles_when_input_is_empty() {
            let mut elements: [usize; 0] = [];

            binary(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn handles_when_input_is_single_element() {
            let mut elements = [0];

            binary(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn does_not_modify_input_when_already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            debug_assert!(elements.is_sorted());

            binary(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn will_swap_elements_if_in_decreasing_order() {
            let mut elements = [1, 0];

            binary(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_odd_length() {
            let mut elements = [2, 1, 0];

            binary(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_even_length() {
            let mut elements = [2, 0, 3, 1];

            binary(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod gnome {
        use super::*;

        #[test]
        fn handles_when_input_is_empty() {
            let mut elements: [usize; 0] = [];

            gnome(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn handles_when_input_is_single_element() {
            let mut elements = [0];

            gnome(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn does_not_modify_input_when_already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            debug_assert!(elements.is_sorted());

            gnome(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn will_swap_elements_if_in_decreasing_order() {
            let mut elements = [1, 0];

            gnome(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_odd_length() {
            let mut elements = [2, 1, 0];

            gnome(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_even_length() {
            let mut elements = [2, 0, 3, 1];

            gnome(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod shell {
        use super::*;

        #[test]
        fn handles_when_input_is_empty() {
            let mut elements: [usize; 0] = [];

            shell(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn handles_when_input_is_single_element() {
            let mut elements = [0];

            shell(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn does_not_modify_input_when_already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            debug_assert!(elements.is_sorted());

            shell(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn will_swap_elements_if_in_decreasing_order() {
            let mut elements = [1, 0];

            shell(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_odd_length() {
            let mut elements = [2, 1, 0];

            shell(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_even_length() {
            let mut elements = [2, 0, 3, 1];

            shell(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }
}
