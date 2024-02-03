//! Implementations of [Heap Sort](https://en.wikipedia.org/wiki/Heapsort).
//!
//! # Performance
//!
//! | Case    | Complexity |
//! | ------- | ---------- |
//! | worst   | n log n    |
//! | average | n log n    |
//! | best    | n log n    |

/// Index of the left child of the node at `index` in a binary heap.
fn left_child(index: usize) -> usize {
    2 * index + 1
}

/// Index of the right child of  the node at`index` in a binary heap.
fn right_child(index: usize) -> usize {
    2 * index + 2
}

/// Index of the parent of the node at `index` in a binary heap.
fn parent(index: usize) -> usize {
    (index - 1) / 2
}

/// Repair a binary heap rooted by the node at index `root`.
fn sift_down<T>(slice: &mut [T], mut root: usize)
where
    T: Ord,
{
    // while root had at least one child
    while let Some(left) = slice.get(left_child(root)) {
        let greatest_child = || -> usize {
            if slice
                .get(right_child(root))
                .is_some_and(|right| left < right)
            {
                right_child(root)
            } else {
                left_child(root)
            }
        }();

        // sift the child down
        if slice[root] < slice[greatest_child] {
            slice.swap(root, greatest_child);
            root = greatest_child;
        } else {
            // node indexed at `root` is the largest element
            return;
        }
    }
}

/// Put elements of a slice in binary heap order.
fn heapify<T>(slice: &mut [T])
where
    T: Ord,
{
    if slice.len() > 1 {
        // parent of last element
        let mut start = parent(slice.len() - 1) + 1;

        while start > 0 {
            // last node not in heap
            start = start - 1;

            // sift down node at `start` such that all nodes whose index is below `start` are in heap order.
            sift_down(slice, start);
        }
    }
}

pub fn sort<T>(slice: &mut [T])
where
    T: Ord,
{
    if !slice.is_empty() {
        heapify(slice);

        let mut end = slice.len();
        while end > 1 {
            end = end - 1;
            slice.swap(0, end);

            // slice[end..] is sorted
            sift_down(&mut slice[..end], 0);
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn empty() {
        let mut slice: [usize; 0] = [];
        sort(&mut slice);
        assert_eq!(slice, []);
    }

    #[test]
    fn one_element() {
        let mut slice = [0];
        sort(&mut slice);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn sorted() {
        let mut slice = [0, 1];
        sort(&mut slice);
        assert_eq!(slice, [0, 1]);
    }
}
