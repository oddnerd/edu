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

/// Merge two lists into a partially overlapping output.
///
/// `slice` is divided as [left..left_end..output..right..right_end]
/// where the inputs are [left..left_end] and [right..right_end]
/// which are merged into [output..right_end].
fn inplace_merge<T: Ord>(
    slice: &mut [T],
    left: usize,
    left_end: usize,
    right: usize,
    right_end: usize,
    output: usize,
) {
    match (slice[..left_end].get(left), slice[..right_end].get(right)) {
        (Some(first), Some(second)) => {
            if first < second {
                slice.swap(output, left);
                inplace_merge(slice, left + 1, left_end, right, right_end, output + 1);
            } else {
                slice.swap(output, right);
                inplace_merge(slice, left, left_end, right + 1, right_end, output + 1);
            }
        }
        (Some(_), None) => {
            slice.swap(output, left);
            inplace_merge(slice, left + 1, left_end, right, right_end, output + 1)
        }
        (None, Some(_)) => {
            slice.swap(output, right);
            inplace_merge(slice, left, left_end, right + 1, right_end, output + 1);
        }
        (None, None) => {}
    }
}

/// Merge sort some slice in-place of another.
///
/// Sort the elements of `from` into the buffer `into` whilst swapping
/// overwirrten elements from `into` over to `from` such that `into` will
/// contain the sorted entries of `from` whereas `from` will hold unordered
/// entried of `into`.
fn inplace_into<T: Ord>(from: &mut [T], into: &mut [T]) {
    if from.len() > 1 {
        let middle = from.len() / 2;
        let (left, right) = from.split_at_mut(middle);
        in_place(left);
        in_place(right);

        {
            let mut first = left.iter_mut().peekable();
            let mut second = right.iter_mut().peekable();

            for element in into {
                match (first.peek_mut(), second.peek_mut()) {
                    (Some(left), Some(right)) => {
                        if left <= right {
                            core::mem::swap(element, *left);
                            _ = first.next();
                        } else {
                            core::mem::swap(element, *right);
                            _ = second.next();
                        }
                    }
                    (Some(left), None) => {
                        core::mem::swap(element, *left);
                        _ = first.next();
                    }
                    (None, Some(right)) => {
                        core::mem::swap(element, *right);
                        _ = second.next();
                    }
                    (None, None) => unreachable!("more output elements than input"),
                };
            }
        }

        // merge::iterative(left, right, into);

        // crate::algorithm::merge::Iterative::new(left.iter_mut(), right.iter_mut())
        //     .zip(into.iter_mut())
        //     .for_each(|(smallest, output)| {
        //         core::mem::swap(smallest, output);
        //     });
    } else if let (Some(mut from), Some(mut into)) = (from.first(), into.first()) {
        core::mem::swap(&mut from, &mut into);
    }
}

/// Sort a `slice` using in-place merge sort.
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
/// use rust::algorithm::sort::comparison::merge::inplace;
/// let mut slice = [3,2,1];
/// inplace(&mut slice);
/// assert_eq!(slice, [1,2,3]);
/// ```
pub fn in_place<T: Ord>(slice: &mut [T]) {
    if slice.len() > 1 {
        let mut middle = (slice.len() + 1) / 2;

        // sort left half into right half
        let (left, right) = slice.split_at_mut(middle);
        inplace_into(left, right);

        while slice[..middle].len() > 1 {
            let sorted = middle;
            middle = (sorted + 1) / 2;

            // sort right fraction into left fraction
            let (left, right) = slice.split_at_mut(middle);
            inplace_into(&mut right[..middle], left);

            // merge sorted left fraction into original sorted right half using
            // space of unsorted elements in-between thereby causing
            // `slice[..middle]` to become the unsorted elements.
            inplace_merge(slice, 0, middle, sorted, slice.len(), middle);
        }

        // first is the only unsorted element, swap it back until sorted
        for index in 1..slice.len() {
            if slice[index] < slice[index - 1] {
                slice.swap(index, index - 1);
            } else {
                break;
            }
        }
    }
}

#[cfg(test)]
mod inplace {
    use super::in_place;

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
