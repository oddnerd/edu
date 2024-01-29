pub fn top_down<T>(slice: &mut [T], auxiliary: &mut [T]) -> ()
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

pub fn bottom_up<T>(slice: &mut [T], auxiliary: &mut [T]) -> ()
where
    T: Ord + Clone,
{
    let mut width: usize = 1;
    loop {
        if width < slice.len() {
            let mut i: usize = 0;

            fn min<T: Ord>(first: T, second: T) -> T {
                if first < second {
                    first
                } else {
                    second
                }
            }

            loop {
                if i < slice.len() {
                    merge(
                        slice,
                        i,
                        min(i + slice.len(), slice.len()),
                        min(i + 2 * width, slice.len()),
                        auxiliary,
                    );
                } else {
                    break;
                }
                i = i + width * 2
            }
        } else {
            break;
        }
        width = 2 * width;
    }

    std::iter::zip(slice, auxiliary).for_each(|(old, new)| {
        *old = new.clone();
    });
}

pub fn merge<T>(a: &mut [T], left: usize, right: usize, end: usize, b: &mut [T]) -> ()
where
    T: Ord + Clone,
{
    let mut i = left;
    let mut j = right;
    let mut k = left;
    loop {
        if k < end {
            // If left run head exists and is <= existing right run head.
            if i < right && (j >= end || a[i] <= a[j]) {
                b[k] = a[i].clone();
                i = i + 1;
            } else {
                b[k] = a[j].clone();
                j = j + 1;
            }
        } else {
            break;
        }
        k += 1;
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
        let mut slice = [9, 8, 7, 6, 5, 4, 3, 2, 1];
        let mut auxiliary = slice.to_vec();
        bottom_up(&mut slice, &mut auxiliary);
        assert_eq!(slice, [1, 2, 3, 4, 5, 6, 7, 8, 9]);
    }

}
