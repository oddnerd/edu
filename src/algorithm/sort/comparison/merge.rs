//! Implementations of [Merge Sort](https://en.wikipedia.org/wiki/Merge_sort).
//!
//! # Performance
//!
//! | Case    | Complexity |
//! | ------- | ---------- |
//! | worst   | n log n    |
//! | average | n log n    |
//! | best    | n log n    |

/// Sort a slice via top-down merge sort.
///
/// <div class="warning">`auxiliary` MUST be a duplicate of `slice`</div>
///
/// Recursively divide `slice` (and corresponding `auxiliary`) into two subsets
/// until themsleves sorted. Merge the sorted sublists by iteratively
/// cloneing the smallest element from `auxiliary` into `slice`.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::merge::top_down;
/// let mut slice = [3,1,5];
/// let mut auxiliary = slice.to_vec();
/// top_down(&mut slice, &mut auxiliary);
/// assert_eq!(slice, [1,3,5]);
/// ```
pub fn top_down<T>(slice: &mut [T], auxiliary: &mut [T])
where
    T: Ord + Clone,
{
    assert!(slice == auxiliary);
    if slice.len() > 1 {
        let (left_auxiliary, right_auxiliary) = auxiliary.split_at_mut(auxiliary.len() / 2);

        let (left_slice, right_slice) = slice.split_at_mut(slice.len() / 2);

        // Alternating `slice`/`auxiliary` prevents unnecessary clone for
        // top-level caller by ensuring `auxiliary` becomes the sorted
        // left/right subslices thenceforth merged into the output (`slice`).
        top_down(left_auxiliary, left_slice);
        top_down(right_auxiliary, right_slice);

        crate::algorithm::merge::MergeIter::new(left_auxiliary.iter(), right_auxiliary.iter())
            .zip(slice)
            .for_each(|(new, old)| {
                *old = new.clone();
            });
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
    fn multiple_swaps() {
        let mut slice = [2, 0, 3, 1];
        let mut auxiliary = slice.clone();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, [0, 1, 2, 3]);
    }
}

/// Sort a slice via bottom-up merge sort.
///
/// <div class="warning">`auxiliary` MUST be a duplicate of `slice`</div>
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
pub fn bottom_up<T>(slice: &mut [T], auxiliary: &mut [T])
where
    T: Ord + Clone,
{
    assert!(slice == auxiliary);
    let mut length: usize = 2;
    while length <= slice.len() {
        let chunks = std::iter::zip(slice.chunks_mut(length), auxiliary.chunks_mut(length));

        for (slice, auxiliary) in chunks {
            let (left, right) = auxiliary.split_at(auxiliary.len() / 2);

            crate::algorithm::merge::MergeIter::new(left.iter(), right.iter())
                .zip(slice.iter_mut())
                .for_each(|(new, old)| {
                    *old = new.clone();
                });

            // propagate sorted `slice` to `auxiliary` for next chunk iteration
            auxiliary
                .iter_mut()
                .zip(slice.iter())
                .for_each(|(old, new)| {
                    *old = new.clone();
                });
        }
        length *= 2;
    }
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
fn inplace_merge<T>(
    slice: &mut [T],
    left: usize,
    left_end: usize,
    right: usize,
    right_end: usize,
    output: usize,
) where
    T: Ord,
{
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
        (None, None) => {
            return;
        }
    }
}

/// Merge sort some slice in-place of another.
///
/// Sort the elements of `from` into the buffer `into` whilst swapping
/// overwirrten elements from `into` over to `from` such that `into` will
/// contain the sorted entries of `from` whereas `from` will hold unordered
/// entried of `into`.
fn inplace_into<T>(from: &mut [T], into: &mut [T])
where
    T: Ord,
{
    if from.len() > 1 {
        let middle = from.len() / 2;
        let (mut left, mut right) = from.split_at_mut(middle);
        inplace(&mut left);
        inplace(&mut right);

        crate::algorithm::merge::MergeIter::new(left.iter_mut(), right.iter_mut())
            .zip(into.iter_mut())
            .for_each(|(smallest, output)| {
                std::mem::swap(smallest, output);
            });
    }
}

/// Sort a slice using O(n log n) in-place merge sort.
///
/// Sort the left half into the right half swapping unsorted elements from
/// the right half into spots sorted from the left half such that the left half
/// contains the unsorted elements from the right half whereas the right half
/// contains the now sorted elements from the left half. Iteratively sort the
/// last half of the unsorted elements into the first half, then merge the
/// now sorted first half with the original sorted right half using the space
/// of the unsorted fraction in-between such that those unsorted elements are
/// moved into spots from the sorted left half for the next iteration.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::merge::inplace;
/// let mut slice = [3,2,1];
/// inplace(&mut slice);
/// assert_eq!(slice, [1,2,3]);
/// ```
pub fn inplace<T>(slice: &mut [T])
where
    T: Ord,
{
    if slice.len() > 1 {
        let mut middle = slice.len() / 2;

        // sort left half into right half
        let (left, right) = slice.split_at_mut(middle);
        inplace_into(left, right);

        while slice[..middle].len() > 1 {
            let end = middle;
            middle = (end + 1) / 2;

            // sort right fraction into left fraction
            let (left, right) = slice.split_at_mut(middle);
            inplace_into(&mut right[..middle], left);

            // merge sorted left fraction into original sorted right half using
            // space of unsorted elements in-between thereby causing
            // `slice[..middle]` to become the unsorted elements.
            inplace_merge(slice, 0, middle, end, slice.len(), middle);
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
    fn multiple_swaps() {
        let mut slice = [2, 0, 3, 1];
        inplace(&mut slice);
        assert_eq!(slice, [0, 1, 2, 3]);
    }

    #[test]
    fn long() {
        let mut slice: Vec<usize> = (0..16).collect();
        let clone = slice.clone();
        slice.reverse();
        inplace(&mut slice);
        assert_eq!(slice, clone);
    }
}
