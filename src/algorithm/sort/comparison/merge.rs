//! Implementations of [Merge Sort](https://en.wikipedia.org/wiki/Merge_sort).

use super::super::super::merge;

/// Sort `elements` via top-down merge sort.
///
/// Recursively divide `elements` into two halves until each contains only
/// a single element and is therefore in sorted order. Then merge both
/// independently sorted halves together thereby sorting them into one
/// larger sorted section which can be passed up the call stack to be merged
/// with another.
///
/// # Panics
/// This method has the precondition that `auxiliary` is a clone of `elements`.
///
/// # Performance
/// This method takes O(N * log N) time and consumes O(log N) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::merge::top_down;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
/// let mut auxiliary = elements.clone();
///
/// top_down(&mut elements, &mut auxiliary);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn top_down<T: Ord>(elements: &mut [T], auxiliary: &mut [T]) {
    debug_assert!(elements == auxiliary, "auxiliary must be clone of elements");

    if elements.len() <= 1 {
        return;
    }

    let (left_input, right_input) = elements.split_at_mut(elements.len() / 2);
    let (left_auxiliary, right_auxiliary) = auxiliary.split_at_mut(auxiliary.len() / 2);

    // Alternating input/auxiliary ensures top-level caller merges into output.
    top_down(left_auxiliary, left_input);
    top_down(right_auxiliary, right_input);

    merge::iterative(left_auxiliary, right_auxiliary, elements);
}

#[cfg(test)]
mod top_down {
    use super::top_down;

    #[test]
    fn empty() {
        let mut slice: [usize; 0] = [];
        let mut auxiliary = slice.clone();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, []);
    }

    #[test]
    fn single() {
        let mut slice = [0];
        let mut auxiliary = slice.clone();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn sorted() {
        let mut slice = [0, 1];
        let mut auxiliary = slice.clone();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn must_swap() {
        let mut slice = [1, 0];
        let mut auxiliary = slice.clone();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn odd_length() {
        let mut slice = [3, 2, 1];
        let mut auxiliary = slice.clone();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, [1, 2, 3]);
    }

    #[test]
    fn multiple_swaps() {
        let mut slice = [2, 0, 3, 1];
        let mut auxiliary = slice.clone();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, [0, 1, 2, 3]);
    }
}

/// Sort `elements` via bottom-up merge sort.
///
/// Consider the input to be adjacent subsections each containing only a single
/// element, therefore each being independently sorted. For each pair of
/// chunks, merge them together into a combined sorted subsection. Repeat
/// until there exists only one sorted section containing all elements.
///
/// # Panics
/// This method has the precondition that `auxiliary` is a clone of `elements`.
///
/// # Performance
/// This method takes (N * log N) time and consumes O(1) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::merge::bottom_up;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
/// let mut auxiliary = elements.clone();
///
/// bottom_up(&mut elements, &mut auxiliary);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn bottom_up<T: Ord>(elements: &mut [T], auxiliary: &mut [T]) {
    debug_assert!(elements == auxiliary, "auxiliary must be clone of elements");

    let Some(bound) = elements.len().checked_ilog2() else {
        debug_assert_eq!(elements.len(), 0, "only condition ilog2 is none");
        return;
    };

    let Some(bound) = bound.checked_add(1) else {
        unreachable!("bound is at most the number of bits in usize");
    };

    for length in (1..=bound).map_while(|exponent| usize::checked_pow(2, exponent)) {
        let elements = elements.chunks_mut(length);
        let auxiliary = auxiliary.chunks_mut(length);

        for (input, output) in elements.zip(auxiliary) {
            let (left, right) = input.split_at_mut(length / 2);

            merge::iterative(left, right, output);

            input.swap_with_slice(output);
        }
    }
}

#[cfg(test)]
mod bottom_up {
    use super::bottom_up;

    #[test]
    fn temporary_test_please_delete_me_or_something() {
        // let mut elements = [0, 5, 2, 3, 1, 4];
        let mut elements = [5, 0, 3, 2, 4, 1];
        let mut auxiliary = elements.clone();

        bottom_up(&mut elements, &mut auxiliary);

        assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
    }

    #[test]
    fn empty() {
        let mut slice: [usize; 0] = [];
        let mut auxiliary = slice.clone();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, []);
    }

    #[test]
    fn single() {
        let mut slice = [0];
        let mut auxiliary = slice.clone();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn sorted() {
        let mut slice = [0, 1];
        let mut auxiliary = slice.clone();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn must_swap() {
        let mut slice = [1, 0];
        let mut auxiliary = slice.clone();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn odd_length() {
        let mut slice = [3, 2, 1];
        let mut auxiliary = slice.clone();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, [1, 2, 3]);
    }

    #[test]
    fn multiple_swaps() {
        let mut slice = [2, 0, 3, 1];
        let mut auxiliary = slice.clone();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, [0, 1, 2, 3]);
    }
}

/// Sort `elements` using in-place merge sort.
///
/// Note that this is non-stable meaning the order of equivalent elements is
/// not preserved.
///
/// Sort the left half of the slice into the right half so the right half is
/// sorted and the left half is unsorted. Thenceforth sort the right half of
/// the unsorted fraction into the left half, merge the sorted fraction into
/// the original sorted right half thereby combining the sorted elements on the
/// right and unsorted on the left, repeating until all elements are sorted.
///
/// # Examples
/// ```
/// todo!()
/// ```
#[allow(clippy::indexing_slicing)]
#[allow(clippy::arithmetic_side_effects)]
#[allow(clippy::many_single_char_names)]
pub fn in_place<T: Ord + core::fmt::Debug>(elements: &mut [T]) {

    /// TODO
    fn merge<T: Ord + core::fmt::Debug>(elements: &mut [T], left: core::ops::Range<usize>, right: core::ops::Range<usize>, mut output: usize) {
        let mut left = left.peekable();
        let mut right = right.peekable();

        while let (Some(first), Some(second)) = (left.peek(), right.peek()) {
            if elements[*first] < elements[*second] {
                let Some(left) = left.next() else {
                    unreachable!("peek was some");
                };

                elements.swap(output, left);
            } else {
                let Some(right) = right.next() else {
                    unreachable!("peek was some");
                };

                elements.swap(output, right);
            }

            output += 1;
        }

        for index in left {
            elements.swap(output, index);
            output += 1;
        }

        for index in right {
            elements.swap(output, index);
            output += 1;
        }
    }

    /// TODO
    fn wsort<T: Ord + core::fmt::Debug>(elements: &mut [T], range: core::ops::Range<usize>, output: usize) {
        if range.len() > 1 {
            let middle = range.start + (range.len() / 2);

            let (left, right) = elements.split_at_mut(middle);
            in_place(left);
            in_place(right);

            merge(elements, range.start..middle, middle..range.end, output);
        } else {
            elements.swap(output, range.start);
        }
    }

    if elements.len() > 1 {
        let middle = elements.len() / 2;
        let mut output = elements.len() - middle;

        wsort(elements, 0..middle, output);

        while output > 2 {
            let middle = output;
            output = (middle + 1) / 2;

            wsort(elements, output..middle, 0);

            merge(elements, 0..(middle - output), middle..elements.len(), output);
        }

        let mut n = output;
        while n > 0 {

            let mut m = n;
            while m < elements.len() && elements[m] < elements[m - 1] {
                elements.swap(m, m - 1);

                m += 1;
            }

            n -= 1;
        }
    }
}

#[cfg(test)]
mod inplace {
    use super::in_place;

    #[test]
    fn temporary_test_please_delete_me_or_something() {
        let mut elements = [5, 0, 3, 2, 4, 1];

        in_place(&mut elements);

        assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
    }

    #[test]
    fn empty() {
        let mut slice: [usize; 0] = [];
        in_place(&mut slice);
        assert_eq!(slice, []);
    }

    #[test]
    fn single() {
        let mut slice = [0];
        in_place(&mut slice);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn sorted() {
        let mut slice = [0, 1];
        in_place(&mut slice);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn must_swap() {
        let mut slice = [1, 0];
        in_place(&mut slice);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn odd_length() {
        let mut slice = [3, 2, 1];
        in_place(&mut slice);
        assert_eq!(slice, [1, 2, 3]);
    }

    #[test]
    fn multiple_swaps() {
        let mut slice = [2, 0, 3, 1];
        in_place(&mut slice);
        assert_eq!(slice, [0, 1, 2, 3]);
    }
}
