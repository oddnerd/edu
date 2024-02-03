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

/// Reorder root of a binary max-heap ordered slice.
///
/// <div class="warning">Assumes children are valid binary max-heaps.</div>
///
/// Swap the first element (current root) with the greatest root of either
/// the left or right child max-heap until the subtree rooted by the first
/// element is itself a valid max-heap.
fn sift_down<T>(slice: &mut [T], root: usize)
where
    T: Ord,
{
    if let Some(left) = slice.get(left_child(root)) {
        let child = || -> usize {
            if slice
                .get(right_child(root))
                .is_some_and(|right| left < right)
            {
                right_child(root)
            } else {
                left_child(root)
            }
        }();

        if slice[child] > slice[root] {
            slice.swap(root, child);
            sift_down(&mut slice[child..], 0)
        }
    }
}

/// Arrange elements of a slice into max heap order.
///
/// Interpret `slice` as a binary tree where, for each node at index i, the
/// left child is at index (2*i+1) and the right child is at index (2*i+2).
/// Reorder the nodes such that all children are less than their parent.
fn max_heapify<T>(slice: &mut [T])
where
    T: Ord,
{
    if slice.len() > 1 {
        // `last` is the parent of the last element hence it is the greatest
        // index of a node in the heap which has children. Since elements
        // within `slice[first..]` are leaves to some subtree rooted by an
        // index in `slice[..=first]`, therefore they can be skipped because
        // [`sift_down`] orders them when the index of their parent is reached.
        let last = parent(slice.len() - 1);

        // By going in reverse, since children of `node` will either be leaves
        // or subtrees already heap ordered, therefore sift it down until the
        // tree rooted at `node` is itself heap ordered.
        for node in (0..=last).rev() {
            sift_down(slice, node);
        }
    }
}

/// Sort a slice via bottom-up heap sort.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::heap::bottom_up;
/// let mut slice = [1, 3, 2];
/// bottom_up(&mut slice);
/// assert_eq!(slice, [1, 2, 3]);
/// ```
pub fn bottom_up<T>(slice: &mut [T])
where
    T: Ord,
{
    max_heapify(slice);

    for end in (0..slice.len()).rev() {
        slice.swap(0, end);

        // slice[end..] is sorted
        sift_down(&mut slice[..end], 0);
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn empty() {
        let mut slice: [usize; 0] = [];
        bottom_up(&mut slice);
        assert_eq!(slice, []);
    }

    #[test]
    fn one_element() {
        let mut slice = [0];
        bottom_up(&mut slice);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn sorted() {
        let mut slice = [0, 1];
        bottom_up(&mut slice);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn swap_necessary() {
        let mut slice = [1, 0];
        bottom_up(&mut slice);
        assert_eq!(slice, [0, 1]);
    }
}
