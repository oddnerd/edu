//! Implementations of [Heap Sort](https://en.wikipedia.org/wiki/Heapsort).

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

mod sift_down {
    use super::*;

    /// Reorder root (first element) of a binary max-heap ordered slice.
    ///
    /// Swap the first element (current root) with the greatest root of either
    /// the left or right child max-heap until the subtree rooted by the first
    /// element is itself a valid max-heap.
    pub(super) fn top_down<T>(slice: &mut [T])
    where
        T: Ord,
    {
        let root = 0;
        if let Some(left) = slice.get(left_child(root)) {
            let child = if slice
                .get(right_child(root))
                .is_some_and(|right| left < right)
            {
                right_child(root)
            } else {
                left_child(root)
            };

            if slice[child] > slice[root] {
                slice.swap(root, child);
                top_down(&mut slice[child..])
            }
        }
    }

    pub(super) fn bottom_up<T>(slice: &mut [T], index: usize)
    where
        T: Ord,
    {
        fn leaf_search<T>(slice: &mut [T], mut index: usize) -> usize
        where
            T: Ord,
        {
            while right_child(index) < slice.len() {
                if slice[right_child(index)] > slice[left_child(index)] {
                    index = right_child(index);
                } else {
                    index = left_child(index);
                }
            }

            if left_child(index) < slice.len() {
                index = left_child(index);
            }

            index
        }

        if !slice.is_empty() {
            let mut leaf = leaf_search(slice, index);
            while slice[index] > slice[leaf] {
                leaf = parent(leaf);
            }
            while leaf > index {
                slice.swap(index, leaf);
                leaf = parent(leaf);
            }
        }
    }
}

mod max_heapify {
    use super::*;

    /// Arrange elements of a slice into max-heap order in O(n log n) time.
    ///
    /// Interpret `slice` as a binary tree where, for each node at index i, the
    /// left child is at index (2*i+1) and the right child is at index (2*i+2).
    /// Reorder the nodes such that all children are less than their parent.
    pub(super) fn bottom_up<T>(slice: &mut [T])
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
                sift_down::top_down(&mut slice[node..]);
            }
        }
    }

    /// Arrange elements of a slice into max-heap order in O(n) time.
    ///
    /// Interpret `slice` as a binary tree where, for each node at index i, the
    /// left child is at index (2*i+1) and the right child is at index (2*i+2).
    /// Reorder the nodes such that all children are less than their parent.
    pub(super) fn top_down<T>(slice: &mut [T])
    where
        T: Ord,
    {
        for leaf in 1..=slice.len() {
            // push leaf into the max-heap
            sift_up(&mut slice[..leaf]);
        }
    }
}

/// Sort a slice via bottom-up heap sort.
///
/// Create bottom order heaps with one parent and two leaves. Iteratively join
/// these heaps by 'sifting down' the element corresponding to their parent in
/// the slice until all elements are within one max-heap.Ordered elements are
/// then popped from the heap by swapping it with a leaf then 'sift down' to
/// preserve order.
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
    max_heapify::bottom_up(slice);

    for end in (0..slice.len()).rev() {
        // max-heap implies the root node is the greatest in the collection,
        // pop it from the max-heap by swapping it with the last element.
        slice.swap(0, end);

        // push the new root into the shrunk max-heap excluding sorted element.
        // sift_down(&mut max_heap[..end]);
        sift_down::bottom_up(&mut slice[..end], 0);
    }
}

#[cfg(test)]
mod bottom_up {
    use super::bottom_up;

    #[test]
    fn empty() {
        let mut slice: [usize; 0] = [];
        bottom_up(&mut slice);
        assert_eq!(slice, []);
    }

    #[test]
    fn single() {
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
    fn must_swap() {
        let mut slice = [1, 0];
        bottom_up(&mut slice);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn odd_length() {
        let mut slice = [3, 2, 1];
        bottom_up(&mut slice);
        assert_eq!(slice, [1, 2, 3]);
    }

    #[test]
    fn multiple_swap() {
        let mut slice = [2, 0, 3, 1];
        bottom_up(&mut slice);
        assert_eq!(slice, [0, 1, 2, 3]);
    }
}

/// Sort a slice via bottom-up heap sort with inline sift-down optimization.
///
/// [`bottom_up`] separates creating the max-heap and using it to iterate the
/// elements in sorted order. In contrast, this implementation combines the two
/// steps into one loop with a conditional. With branch prediction and inline
/// expansion of 'sifting down', this implementation would likely have different
/// runtime characteristics.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::heap::bottom_up_inline;
/// let mut slice = [3, 2, 1];
/// bottom_up_inline(&mut slice);
/// assert_eq!(slice, [1, 2, 3]);
/// ```
pub fn bottom_up_inline<T>(slice: &mut [T])
where
    T: Ord,
{
    // start at the parent of the last element which is the greatest
    // index of a node in the heap which has children. Since elements
    // within `slice[heap..]` are leaves to some subtree rooted by an
    // index in `slice[..=heap]`, therefore they can be skipped because
    // [`sift_down`] orders them when the index of their parent is reached.
    let mut heap = slice.len() / 2;

    // slice[left_unsorted..] is sorted.
    let mut left_unsorted = slice.len();

    while left_unsorted > 1 {
        // if the heap has yet to be constructed.
        if heap > 0 {
            heap -= 1;
        }
        // max-heap implies the root node is the greatest in the collection,
        // pop it from the max-heap by swapping it with the last element.
        else {
            left_unsorted -= 1;
            slice.swap(left_unsorted, 0);
        }

        // `slice[heap]` is either the next element to heapify, or the leaf
        // swapped for the maximum element of the constructed max-heap.
        sift_down::top_down(&mut slice[heap..left_unsorted]);
    }
}

#[cfg(test)]
mod bottom_up_inline {
    use super::bottom_up_inline;

    #[test]
    fn empty() {
        let mut slice: [usize; 0] = [];
        bottom_up_inline(&mut slice);
        assert_eq!(slice, []);
    }

    #[test]
    fn single() {
        let mut slice = [0];
        bottom_up_inline(&mut slice);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn sorted() {
        let mut slice = [0, 1];
        bottom_up_inline(&mut slice);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn must_swap() {
        let mut slice = [1, 0];
        bottom_up_inline(&mut slice);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn odd_length() {
        let mut slice = [3, 2, 1];
        bottom_up_inline(&mut slice);
        assert_eq!(slice, [1, 2, 3]);
    }

    #[test]
    fn multiple_swap() {
        let mut slice = [2, 0, 3, 1];
        bottom_up_inline(&mut slice);
        assert_eq!(slice, [0, 1, 2, 3]);
    }
}

/// Reorder last leaf of a binary max-heap ordered slice.
///
/// Swap the last element (final leaf) with its parent until it is ordered
/// within the max-heap.
fn sift_up<T>(slice: &mut [T])
where
    T: Ord,
{
    if slice.len() > 1 {
        let current_index = slice.len() - 1;
        let parent_index = parent(current_index);

        if let (Some(current), Some(parent)) = (slice.get(current_index), slice.get(parent_index)) {
            if parent < current {
                slice.swap(current_index, parent_index);
                sift_up(&mut slice[..=parent_index]);
            }
        }
    }
}

/// Sort a slice via top-down heap sort.
///
/// Create one max-heap at the start of the slice and then push each successive
/// element into it by 'sifting up'. Ordered elements are then popped from the
/// heap by swapping it with a leaf then 'sifting down' to preserve the heap.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::heap::top_down;
/// let mut slice = [3, 2, 1];
/// top_down(&mut slice);
/// assert_eq!(slice, [1, 2, 3]);
/// ```
pub fn top_down<T>(slice: &mut [T])
where
    T: Ord,
{
    max_heapify::top_down(slice);

    for end in (0..slice.len()).rev() {
        // max-heap implies the root node is the greatest in the collection,
        // pop it from the max-heap by swapping it with the last element.
        slice.swap(0, end);

        // push the new root into the shrunk max-heap excluding sorted element.
        sift_down::top_down(&mut slice[..end]);
    }
}

#[cfg(test)]
mod top_down {
    use super::top_down;

    #[test]
    fn empty() {
        let mut slice: [usize; 0] = [];
        top_down(&mut slice);
        assert_eq!(slice, []);
    }

    #[test]
    fn single() {
        let mut slice = [0];
        top_down(&mut slice);
        assert_eq!(slice, [0]);
    }

    #[test]
    fn sorted() {
        let mut slice = [0, 1];
        top_down(&mut slice);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn must_swap() {
        let mut slice = [1, 0];
        top_down(&mut slice);
        assert_eq!(slice, [0, 1]);
    }

    #[test]
    fn odd_length() {
        let mut slice = [3, 2, 1];
        top_down(&mut slice);
        assert_eq!(slice, [1, 2, 3]);
    }

    #[test]
    fn multiple_swap() {
        let mut slice = [2, 0, 3, 1];
        top_down(&mut slice);
        assert_eq!(slice, [0, 1, 2, 3]);
    }
}
