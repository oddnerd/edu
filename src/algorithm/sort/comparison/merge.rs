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

        let merger =
            crate::algorithm::merge::MergeIter::new(left_auxiliary.iter(), right_auxiliary.iter());

        std::iter::zip(slice, merger).for_each(|(old, new)| {
            *old = new.clone();
        });
    }
}

#[cfg(test)]
mod top_down_tests {
    use super::*;

    #[test]
    fn empty() {
        let mut slice: [usize; 0] = [];
        let mut auxiliary = slice.to_vec();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, []);
    }

    #[test]
    fn one() {
        let mut slice = [0];
        let mut auxiliary = slice.to_vec();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn two() {
        let mut slice = [2, 1];
        let mut auxiliary = slice.to_vec();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, [1, 2]);
    }

    #[test]
    fn multiple() {
        let mut slice = [3, 2, 1];
        let mut auxiliary = slice.to_vec();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, [1, 2, 3]);
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
    T: Ord + Clone + std::fmt::Debug,
{
    assert!(slice == auxiliary);
    let mut length: usize = 2;
    while length <= slice.len() {
        let chunks = std::iter::zip(slice.chunks_mut(length), auxiliary.chunks_mut(length));

        for (slice, auxiliary) in chunks {
            let (left, right) = auxiliary.split_at(auxiliary.len() / 2);

            let merger = crate::algorithm::merge::MergeIter::new(left.iter(), right.iter());

            // merge from `auxiliary` into `slice`
            std::iter::zip(slice.iter_mut(), merger).for_each(|(old, new)| {
                *old = new.clone();
            });

            // propagate sorted `slice` to `auxiliary` for next chunk iteration
            std::iter::zip(auxiliary.iter_mut(), slice.iter()).for_each(|(old, new)| {
                *old = new.clone();
            });
        }
        length *= 2;
    }
}

#[cfg(test)]
mod bottom_up_tests {
    use super::*;

    #[test]
    fn empty() {
        let mut slice: [usize; 0] = [];
        let mut auxiliary = slice.to_vec();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, []);
    }

    #[test]
    fn one() {
        let mut slice = [0];
        let mut auxiliary = slice.to_vec();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn two() {
        let mut slice = [2, 1];
        let mut auxiliary = slice.to_vec();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, [1, 2]);
    }

    #[test]
    fn multiple() {
        let mut slice: Vec<i32> = (0..4).collect();
        let copy = slice.clone();
        slice.reverse();
        let mut auxiliary = slice.to_vec();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, copy);
    }
}

/// Merge two lists into a partially overlapping output.
///
/// `slice` is divided as [left..left_end..output..right..right_end]
/// where the inputs are [left..left_end] and [right..right_end]
/// which are merged into [output..right_end].
fn inplace_merge<T>(
    slice: &mut [T],
    mut left: usize,
    left_end: usize,
    mut right: usize,
    right_end: usize,
    mut output: usize,
) where
    T: Ord + Clone,
{
    while left < left_end && right < right_end {
        if slice[left] < slice[right] {
            (slice[output], slice[left]) = (slice[left].clone(), slice[output].clone());
            left += 1;
        } else {
            (slice[output], slice[right]) = (slice[right].clone(), slice[output].clone());
            right += 1;
        }
        output += 1;
    }
    while left < left_end {
        (slice[output], slice[left]) = (slice[left].clone(), slice[output].clone());
        output += 1;
        left += 1;
    }
    while right < right_end {
        (slice[output], slice[right]) = (slice[right].clone(), slice[output].clone());
        output += 1;
        right += 1;
    }
}

/// Mergesort some slice in-place of another.
///
/// `output` will contain the sorted entries of `input`
/// whereas `input` will hold unsorted entried of `output`.
fn inplace_with<T>(input: &mut [T], output: &mut [T])
where
    T: Ord + Clone,
{
    if !input.is_empty() {
        let middle = input.len() / 2;
        let (mut left, mut right) = input.split_at_mut(middle);
        inplace(&mut left);
        inplace(&mut right);

        let merger = crate::algorithm::merge::MergeIter::new(left.iter_mut(), right.iter_mut());

        std::iter::zip(merger, output.iter_mut()).for_each(|(smallest, output)| {
            (*smallest, *output) = (output.clone(), smallest.clone())
        });
    }
}

/// Sort a slice using in-place merge sort.
///
/// O(n log n) based on "Practical in-place mergesort".
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
    T: Ord + Clone,
{
    if slice.len() > 1 {
        let middle = slice.len() / 2;
        let mut output = slice.len() - middle;

        // sort slice[..middle] into slice[output..]
        let (read, write) = slice.split_at_mut(middle);
        inplace_with(read, &mut write[output - middle..]);

        while output > 2 {
            let middle = output;
            output = (middle + 1) / 2;

            // sort slice[output..middle] into slice[..output]
            let (left, right) = slice.split_at_mut(output);
            inplace_with(&mut right[..middle - output], left);

            inplace_merge(slice, 0, middle - output, middle, slice.len(), output);
        }
    }
}

#[cfg(test)]
mod inplace_tests {
    use super::*;

    #[test]
    fn empty() {
        let mut slice: [usize; 0] = [];
        inplace(&mut slice);
        assert_eq!(slice, []);
    }

    #[test]
    fn one() {
        let mut slice = [0];
        inplace(&mut slice);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn two() {
        let mut slice = [1, 0];
        inplace(&mut slice);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn multiple() {
        let mut slice: Vec<i32> = (0..10).collect();
        let copy = slice.clone();
        slice.reverse();
        inplace(&mut slice);
        assert_eq!(slice, copy);
    }
}
