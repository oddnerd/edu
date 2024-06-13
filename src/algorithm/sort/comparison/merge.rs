//! Implementations of [Merge Sort](https://en.wikipedia.org/wiki/Merge_sort).

use super::super::super::merge;

/// Sort a `slice` via top-down merge sort.
///
/// Recursively divide `slice` into two sub-slices until each contains only
/// a single element and is therefore in sorted order. Then merge both
/// independently sorted sub-slices together thereby sorting them into one
/// larger sorted slice which can be passed up the call stack to be merged
/// with another.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::merge::top_down;
/// let mut slice = [3,1,5];
/// let mut auxiliary = slice.to_vec();
/// top_down(&mut slice, &mut auxiliary);
/// assert_eq!(slice, [1,3,5]);
/// ```
pub fn top_down<T: Ord + Clone>(slice: &mut [T], auxiliary: &mut [T]) {
    assert!(slice == auxiliary);
    if slice.len() > 1 {
        let (left_auxiliary, right_auxiliary) = auxiliary.split_at_mut(auxiliary.len() / 2);

        let (left_slice, right_slice) = slice.split_at_mut(slice.len() / 2);

        // Alternating `slice`/`auxiliary` prevents unnecessary clone for
        // top-level caller by ensuring `auxiliary` becomes the sorted
        // left/right subslices thenceforth merged into the output (`slice`).
        top_down(left_auxiliary, left_slice);
        top_down(right_auxiliary, right_slice);

        merge::iterative(left_auxiliary, right_auxiliary, slice);
    }
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

/// Sort a `slice` via bottom-up merge sort.
///
/// Iteratively merge chunks of 2<sup>n</sup> elements. Start by merging
/// single elements into chunks of two elements, then merge those into chunks
/// of four elements, then merge all those chunks, so on and so forth.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::merge::bottom_up;
/// let mut slice = [3,1,5];
/// let mut auxiliary = slice.to_vec();
/// bottom_up(&mut slice, &mut auxiliary);
/// assert_eq!(slice, [1,3,5]);
/// ```
pub fn bottom_up<T: Ord + Clone>(slice: &mut [T], auxiliary: &mut [T]) {
    assert!(slice == auxiliary);

    // merge `from[..middle]` and `from[middle..]` into `into`
    fn merge<T: Ord + Clone>(into: &mut [T], from: &mut [T]) {
        let middle = (from.len() + 1) / 2;
        let (left, right) = from.split_at_mut(middle);

        // merging those two sorted subslices sorts them together
        merge::iterative(left, right, into);
    }

    // interpret each slice as chunks (subslices) of size `length`.
    let mut length = 2;

    // if the length of `slice` is not exactly some 2^n, the full loop
    // would exit leaving one final merge necessary so might as well
    // exit when length implies theres only two sorted subslices left.
    while length <= (slice.len() + 1) / 2 {
        let chunks = slice.chunks_mut(length).zip(auxiliary.chunks_mut(length));

        for (slice, auxiliary) in chunks {
            // we assume from previous iteration each chunk is split
            // at the middle into sorted subslices.
            merge(slice, auxiliary);

            // clone the result into `auxiliary` for next merge iteration
            slice
                .iter()
                .zip(auxiliary.iter_mut())
                .for_each(|(new, old)| {
                    *old = new.clone();
                });
        }

        // next iteration can merge two subslices of the current length.
        length *= 2;
    }

    merge(slice, auxiliary);
}

#[cfg(test)]
mod bottom_up {
    use super::bottom_up;

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
        inplace(left);
        inplace(right);

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
pub fn inplace<T: Ord>(slice: &mut [T]) {
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
    use super::inplace;

    #[test]
    fn empty() {
        let mut slice: [usize; 0] = [];
        inplace(&mut slice);
        assert_eq!(slice, []);
    }

    #[test]
    fn single() {
        let mut slice = [0];
        inplace(&mut slice);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn sorted() {
        let mut slice = [0, 1];
        inplace(&mut slice);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn must_swap() {
        let mut slice = [1, 0];
        inplace(&mut slice);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn odd_length() {
        let mut slice = [3, 2, 1];
        inplace(&mut slice);
        assert_eq!(slice, [1, 2, 3]);
    }

    #[test]
    fn multiple_swaps() {
        let mut slice = [2, 0, 3, 1];
        inplace(&mut slice);
        assert_eq!(slice, [0, 1, 2, 3]);
    }
}
