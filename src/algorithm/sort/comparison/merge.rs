

pub fn sort_with<T: Ord + Clone>(slice: &mut [T], auxiliary: &mut [T]) -> () {
    if slice.len() > 1 {
        let (left_aux, right_aux) = auxiliary.split_at_mut(auxiliary.len() / 2);

        let (left_slice, right_slice) = slice.split_at_mut(slice.len() / 2);

        sort_with(left_aux, left_slice);
        sort_with(right_aux, right_slice);

        let merger = crate::algorithm::merge::MergeIter::new(left_aux.iter(), right_aux.iter());

        std::iter::zip(slice.iter_mut(), merger).for_each(|(old, new)| {
            *old = new.clone();
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sort_with_empty() {
        let mut slice: [usize; 0] = [];
        let mut auxiliary = slice.to_vec();
        sort_with(&mut slice, &mut auxiliary);
        assert_eq!(slice, []);
    }

    #[test]
    fn sort_with_one() {
        let mut slice = [0];
        let mut auxiliary = slice.to_vec();
        sort_with(&mut slice, &mut auxiliary);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn sort_with_two() {
        let mut slice = [2, 1];
        let mut auxiliary = slice.to_vec();
        sort_with(&mut slice, &mut auxiliary);
        assert_eq!(slice, [1, 2]);
    }

    #[test]
    fn sort_with_multiple() {
        let mut slice = [3, 2, 1];
        let mut auxiliary = slice.to_vec();
        sort_with(&mut slice, &mut auxiliary);
        assert_eq!(slice, [1, 2, 3]);
    }
}
