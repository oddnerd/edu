//! Implementations of [Merge Sort](https://en.wikipedia.org/wiki/Merge_sort).
//!
//! # Performance
//!
//! | Case    | Complexity |
//! | ------- | ---------- |
//! | worst   | n log n    |
//! | average | n log n    |
//! | best    | n log n    |

/// Sort `slice` using duplicate `auxiliary` memory.
///
/// Recursively divide `slice`, sort subslices, and merge the result.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::merge::top_down;
/// let mut slice = [3,1,5];
/// let mut auxiliary = slice.to_vec();
/// top_down(&mut slice, &mut auxiliary);
/// ```
pub fn top_down<T>(slice: &mut [T], auxiliary: &mut [T])
where
    T: Ord + Clone,
{
    if slice.len() > 1 {
        assert!(slice.len() == auxiliary.len());
        let (left_auxiliary, right_auxiliary) = auxiliary.split_at_mut(auxiliary.len() / 2);

        let (left_slice, right_slice) = slice.split_at_mut(slice.len() / 2);

        // auxiliary becomes the sorted left/right slices to be merged,
        // alternate input/auxiliary to avoid additional clone
        top_down(left_auxiliary, left_slice);
        top_down(right_auxiliary, right_slice);

        let merger =
            crate::algorithm::merge::MergeIter::new(left_auxiliary.iter(), right_auxiliary.iter());

        std::iter::zip(slice, merger).for_each(|(old, new)| {
            *old = new.clone();
        });
    }
}

/// Sort `slice` using duplicate `auxiliary` memory.
///
/// Iteratively merge elements into larger groups.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::merge::bottom_up;
/// let mut slice = [3,1,5];
/// let mut auxiliary = slice.to_vec();
/// bottom_up(&mut slice, &mut auxiliary);
/// ```
pub fn bottom_up<T>(slice: &mut [T], auxiliary: &mut [T])
where
    T: Ord + Clone + std::fmt::Debug,
{
    let mut length: usize = 2;
    while length <= slice.len() {
        let chunks = std::iter::zip(slice.chunks_mut(length), auxiliary.chunks_mut(length));

        for (slice, auxiliary) in chunks {
            let (left, right) = auxiliary.split_at(length / 2);

            let merger = crate::algorithm::merge::MergeIter::new(left.iter(), right.iter());

            // merge from auxiliary into slice
            std::iter::zip(slice.iter_mut(), merger).for_each(|(old, new)| {
                *old = new.clone();
            });

            // propogate merged slice to auxiliary for when next merged
            std::iter::zip(auxiliary.iter_mut(), slice.iter()).for_each(|(old, new)| {
                *old = new.clone();
            });
        }
        length *= 2;
    }
}

fn wmerge<T>(
    slice: &mut [T],
    mut left: usize,
    left_end: usize,
    mut right: usize,
    right_end: usize,
    mut output: usize,
) where
    T: Ord + Clone + std::fmt::Debug,
{
    println!(
        "wmerge({:?}, {:?}, {:?})",
        &slice[left..left_end],
        &slice[right..right_end],
        &slice[output..]
    );

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

fn wsort<T>(slice: &mut [T], mut begin: usize, end: usize, mut output: usize)
where
    T: Ord + Clone + std::fmt::Debug,
{
    println!("wsort({:?}, {:?})", &slice[begin..end], &slice[output..]);

    let len = end - begin;
    if len > 1 {
        let middle = begin + len / 2;
        imsort(slice, begin, middle);
        imsort(slice, middle, end);
        wmerge(slice, begin, middle, middle, end, output);
    } else {
        while begin < end {
            (slice[begin], slice[output]) = (slice[output].clone(), slice[begin].clone());
            begin += 1;
            output += 1;
        }
    }
}

fn imsort<T>(slice: &mut [T], begin: usize, end: usize)
where
    T: Ord + Clone + std::fmt::Debug,
{
    println!("imsort({:?})", &slice[begin..end]);

    let slice = &mut slice[begin..end];
    let end = slice.len();

    if slice.len() > 1 {
        let middle = slice.len() / 2;
        let mut output = end - middle;

        // last half contains sorted elements???
        wsort(slice, 0, middle, output);

        while output > 2 {
            let middle = output;
            output = (middle + 1) / 2;

            // first half of the previous working area contains sorted elements???
            wsort(slice, output, middle, 0);

            wmerge(slice, begin, middle - output, middle, end, output);
        }
        // switch to insertion sort???

        // for (n = w; n > l; --n)
        for n in (1..=output).rev() {
            // for (m = n; m < u && xs[m] < xs[m - 1]; ++m)
            for m in n..end {
                if slice[m] < slice[m - 1] {
                    (slice[m], slice[m - 1]) = (slice[m - 1].clone(), slice[m].clone());
                }
            }
        }
    }
}

#[cfg(test)]
mod inplace_tests {
    use super::*;

    #[test]
    fn empty() {
        let mut slice: [usize; 0] = [];
        imsort(&mut slice, 0, 1);
        assert_eq!(slice, []);
    }

    #[test]
    fn one() {
        let mut slice = [0];
        imsort(&mut slice, 0, 1);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn two() {
        let mut slice = [1, 0];
        imsort(&mut slice, 0, 2);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn multiple() {
        let mut slice: Vec<i32> = (0..10).collect();
        let copy = slice.clone();
        slice.reverse();
        imsort(&mut slice, 0, 10);
        assert_eq!(slice, copy);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn top_down_empty() {
        let mut slice: [usize; 0] = [];
        let mut auxiliary = slice.to_vec();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, []);
    }

    #[test]
    fn top_down_one() {
        let mut slice = [0];
        let mut auxiliary = slice.to_vec();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn top_down_two() {
        let mut slice = [2, 1];
        let mut auxiliary = slice.to_vec();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, [1, 2]);
    }

    #[test]
    fn top_down_multiple() {
        let mut slice = [3, 2, 1];
        let mut auxiliary = slice.to_vec();
        top_down(&mut slice, &mut auxiliary);
        assert_eq!(slice, [1, 2, 3]);
    }

    #[test]
    fn bottom_up_empty() {
        let mut slice: [usize; 0] = [];
        let mut auxiliary = slice.to_vec();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, []);
    }

    #[test]
    fn bottom_up_one() {
        let mut slice = [0];
        let mut auxiliary = slice.to_vec();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn bottom_up_two() {
        let mut slice = [2, 1];
        let mut auxiliary = slice.to_vec();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, [1, 2]);
    }

    #[test]
    fn bottom_up_multiple() {
        let mut slice: Vec<i32> = (0..4).collect();
        let copy = slice.clone();
        slice.reverse();
        let mut auxiliary = slice.to_vec();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, copy);
    }
}
