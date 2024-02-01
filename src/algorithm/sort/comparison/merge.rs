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

fn wsort<T>(slice: &mut [T], mut l: usize, u: usize, mut w: usize)
where
    T: Ord + Clone,
{
    if slice.len() > 1 {
        let middle = slice.len() / 2;
        let (left, right) = slice.split_at_mut(middle);
        inplace(left);
        inplace(right);
        crate::algorithm::merge::inplace(slice, middle, w);
    } else {
        while l < u {
            (slice[l], slice[w]) = (slice[w].clone(), slice[l].clone());
            l += 1;
            w += 1;
        }
    }
}

pub fn inplace<T>(slice: &mut [T])
where
    T: Ord + Clone,
{
    if slice.len() > 1 {
        let middle = slice.len() / 2;
        let mut w = slice.len() - middle;
        wsort(slice, 0, middle, w);

        while w  > 2 {
            let n = w;
            w = (n + 1) / 2;
            wsort(slice, w, n, 0);
            crate::algorithm::merge::inplace(slice, n, w);
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
        let mut slice = [1,0];
        inplace(&mut slice);
        assert_eq!(slice, [0,1]);
    }

    #[test]
    fn multiple() {
        let mut slice: Vec<i32> = (0..4).collect();
        let copy = slice.clone();
        slice.reverse();
        inplace(&mut slice);
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
