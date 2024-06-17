//! Implementations of [Heap Sort](https://en.wikipedia.org/wiki/Heapsort).

/// Sort `elements` via bottom-up heap sort.
///
/// Starting from lone elements which are themselves max-heap ordered,
/// iteratively join these subtrees by sifting down the element corresponding
/// to their parent until all elements are ordered. The max element (the root)
/// can then be swapped with the leaf with the highest index thereby placing it
/// in sorted order, sifting down the leaf to maintain ordering of the heap.
///
/// # Performance
/// This method takes O(N * log N) time and consumes O(1) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::heap::bottom_up;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// bottom_up(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn bottom_up<T: Ord>(elements: &mut [T]) {
    // Order `elements` in max-heap order, hence `elements[0]` is the greatest.
    construct_heap::bottom_up(elements);

    for sorted in (0..elements.len()).rev() {
        // Place the greatest element not yet sorted into sorted order.
        elements.swap(0, sorted);

        let Some(heap) = elements.get_mut(..sorted) else {
            unreachable!("loop ensures within bounds");
        };

        // Sift down the leaf into the max-heap (excluding sorted elements).
        sift_down::bottom_up(heap);
    }
}

/// Sort `elements` via bottom-up heap sort with inline sift-down optimization.
///
/// The implementation of [`bottom_up`] first creates a max-heap, and then
/// separately uses that structure to obtain elements in sorted order thereby
/// having two independent execution paths which ultimately invoke
/// `sift_down`. In contrast, this implementation combines both steps with
/// one shared execution path which would likely result in different runtime
/// characteristics given branch prediction and potential inline expansion.
///
/// /// # Performance
/// This method takes O(N * log N) time and consumes O(1) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::heap::inline;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// inline(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn inline<T: Ord>(elements: &mut [T]) {
    // This is the current root of the heap. It starts at the last parent
    // since the leaves will be heap-ordered by sifting down their parent.
    let mut root = elements.len() / 2;

    // This is how many elements remain in the heap and have yet to be moved
    // into sorted order. This implies `remaining_unsorted..` are sorted.
    let mut remaining_unsorted = elements.len();

    while remaining_unsorted > 1 {
        if root > 0 {
            // The heap has yet to be constructed, and this iteration will
            // sift down the new root at index `heap` into the existing heap.
            if let Some(decremented) = root.checked_sub(1) {
                root = decremented;
            } else {
                unreachable!("this branch is not executed when the variable becomes zero");
            }
        } else {
            if let Some(decremented) = remaining_unsorted.checked_sub(1) {
                remaining_unsorted = decremented;
            } else {
                unreachable!("the loop exits when the variable becomes zero");
            }

            // The heap has been constructed, hence `elements[0]` is the max
            // element which can therefore be swapped into sorted order, and
            // this iteration will sift down the leaf swapped with the root.
            elements.swap(remaining_unsorted, 0);
        }

        let Some(heap) = elements.get_mut(root..remaining_unsorted) else {
            unreachable!("both bounds are less than the number of elements");
        };

        sift_down::top_down(heap);
    }
}

/// Sort `elements` via top-down heap sort.
///
/// Create one max-heap containing the first element, add the next element as a
/// leaf to that heap sifting it up as necessary, repeating until all elements
/// are ordered. The max element (the root) can then be swapped with the leaf
/// with the highest index thereby placing it in sorted order, sifting down the
/// leaf to maintain ordering of the heap.
///
/// # Performance
/// This method takes O(N * log N) time and consumes O(1) memory.
///
/// # Examples
/// ```
/// use rust::algorithm::sort::comparison::heap::top_down;
///
/// let mut elements = [0, 5, 2, 3, 1, 4];
///
/// top_down(&mut elements);
///
/// assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
/// ```
pub fn top_down<T: Ord>(elements: &mut [T]) {
    // Order `elements` in max-heap order, hence `elements[0]` is the greatest.
    construct_heap::top_down(elements);

    for sorted in (0..elements.len()).rev() {
        // Place the greatest element not yet sorted into sorted order.
        elements.swap(0, sorted);

        let Some(heap) = elements.get_mut(..sorted) else {
            unreachable!("loop ensures within bounds");
        };

        // Sift down the leaf into the max-heap (excluding sorted elements).
        sift_down::top_down(heap);
    }
}

/// Index of the left child of the node at `index` in a binary heap.
///
/// # Performance
/// This method takes O(1) time and consumes O(1) memory.
#[inline]
fn left_child(index: usize) -> Option<usize> {
    index.checked_mul(2).and_then(|index| index.checked_add(1))
}

/// Index of the right child of the node at `index` in a binary heap.
///
/// # Performance
/// This method takes O(1) time and consumes O(1) memory.
#[inline]
fn right_child(index: usize) -> Option<usize> {
    index.checked_mul(2).and_then(|index| index.checked_add(2))
}

/// Index of the parent of the node at `index` in a binary heap.
///
/// # Performance
/// This method takes O(1) time and consumes O(1) memory.
#[inline]
fn parent(index: usize) -> Option<usize> {
    index.checked_sub(1).map(|index| index / 2)
}

/// Sift the last leaf of a `max_heap` up to the correct position.
///
/// Swap the leaf with its parent until the parent is greater.
///
/// # Performance
/// This method takes O(log N) time and consumes O(1) memory.
fn sift_up<T: Ord>(max_heap: &mut [T]) {
    let Some(mut current_index) = max_heap.len().checked_sub(1) else {
        debug_assert_eq!(max_heap.len(), 0, "only condition its none");
        return;
    };

    while current_index > 0 {
        let Some(current_element) = max_heap.get(current_index) else {
            unreachable!("index only decreases, cannot be out of bounds");
        };

        let Some(parent_index) = parent(current_index) else {
            unreachable!("the current index is non-zero");
        };

        let Some(parent_element) = max_heap.get(parent_index) else {
            unreachable!("parent is between zero and current, thus in bounds");
        };

        if parent_element < current_element {
            max_heap.swap(current_index, parent_index);
            current_index = parent_index;
        } else {
            break;
        }
    }
}

/// Move a misplaced node down a heap into the correct level.
mod sift_down {
    use super::left_child;
    use super::parent;
    use super::right_child;

    /// Sift the root of a binary `max_heap` down to the correct position.
    ///
    /// Swap the current root with the greatest child until both children are
    /// less than that root, thereby repairing a max-heap with invalid root.
    ///
    /// # Performance
    /// This method takes O(log N) time and consumes O(1) memory.
    pub(super) fn top_down<T: Ord>(max_heap: &mut [T]) {
        let mut root_index = 0;

        loop {
            let (Some(left_child), Some(right_child)) = (left_child(root_index), right_child(root_index)) else {
                unreachable!("loop prevents a root without children big enough to overflow");
            };

            let child_index = match (max_heap.get(left_child), max_heap.get(right_child)) {
                (Some(left), Some(right)) => {
                    if left < right {
                        right_child
                    } else {
                        left_child
                    }
                },
                (Some(_), None) => left_child,
                (None, Some(_)) => unreachable!("left has smaller index"),
                (None, None) => break,
            };

            let (Some(root_element), Some(child_element)) = (max_heap.get(root_index), max_heap.get(child_index)) else {
                unreachable!("in the loop => child exists => root exists");
            };

            if root_element < child_element {
                max_heap.swap(root_index, child_index);
                root_index = child_index;
            } else {
                break;
            }
        }
    }

    /// Sift the root of a binary `max_heap` down to the correct position.
    ///
    /// Traverse the heap down to the leaves (this is presumably where the
    /// current root value came from), and then traverse upward a node is found
    /// which is greater than the value being sifted down.
    ///
    /// This uses fewer comparison than [`top_down`], but will likely have
    /// worse performance for cheap comparisons.
    ///
    /// # Performance
    /// This method takes O(log N) time and consumes O(1) memory.
    pub(super) fn bottom_up<T: Ord>(max_heap: &mut [T]) {
        let mut current = 0;

        // Traverse down to leaf where the smallest possible value goes.
        loop {
            let (Some(left_child), Some(right_child)) = (left_child(current), right_child(current)) else {
                unreachable!("loop prevents a root without children big enough to overflow");
            };

            current = match (max_heap.get(left_child), max_heap.get(right_child)) {
                (Some(left), Some(right)) => {
                    if right > left {
                        right_child
                    } else {
                        left_child
                    }
                }
                (Some(_), None) => left_child,
                (None, Some(_)) => unreachable!("left has smaller index"),
                (None, None) => break,
            }
        }

        // Traverse upwards from that leaf to find where root should go.
        loop {
            let Some(root) = max_heap.first() else {
                return;
            };

            let Some(element) = max_heap.get(current) else {
                unreachable!("above loop will ensure within bounds");
            };

            if root > element {
                let Some(parent) = parent(current) else {
                    unreachable!("loop exits before `root == 0`");
                };

                current = parent;
            } else {
                break;
            }
        }

        // Swap root into that position and propagate upwards.
        while current > 0 {
            max_heap.swap(0, current);

            let Some(parent) = parent(current) else {
                unreachable!("loop exits upon `root == 0`");
            };

            current = parent;
        }
    }
}

/// Construct a binary max-heap (also known as heapify).
mod construct_heap {
    use super::sift_down;
    use super::sift_up;

    /// Arrange `element` into max-heap (children less than parent) order.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    pub(super) fn bottom_up<T: Ord>(elements: &mut [T]) {
        // All leaves will be ordered when their parent is sifted down.
        let last_parent = elements.len() / 2;

        for parent in (0..=last_parent).rev() {
            let Some(heap) = elements.get_mut(parent..) else {
                unreachable!("loop condition ensures in bounds");
            };

            // The children of `node` are already heap ordered, so sift down.
            sift_down::top_down(heap);
        }
    }

    /// Arrange `element` into max-heap (children less than parent) order.
    ///
    /// # Performance
    /// This method takes O(N * log N) time and consumes O(1) memory.
    pub(super) fn top_down<T: Ord>(elements: &mut [T]) {
        for leaf in 1..=elements.len() {
            let Some(heap) = elements.get_mut(..leaf) else {
                unreachable!("loop condition ensures in bounds");
            };

            // The ancestors of `leaf` are already heap ordered, so sift up.
            sift_up(heap);
        }
    }
}

#[cfg(test)]
#[allow(
    clippy::undocumented_unsafe_blocks,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::assertions_on_result_states,
    clippy::indexing_slicing
)]
mod test {
    use super::*;

    mod bottom_up {
        use super::*;

        #[test]
        fn empty() {
            let mut elements = [usize::default(); 0];

            bottom_up(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            bottom_up(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            bottom_up(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            bottom_up(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            bottom_up(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            bottom_up(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod inline {
        use super::*;

        #[test]
        fn empty() {
            let mut elements = [usize::default(); 0];

            inline(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            inline(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            inline(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            inline(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            inline(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            inline(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod top_down {
        use super::*;

        #[test]
        fn empty() {
            let mut elements = [usize::default(); 0];

            top_down(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn single_element() {
            let mut elements = [0];

            top_down(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];

            top_down(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn must_swap() {
            let mut elements = [1, 0];

            top_down(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn odd_length() {
            let mut elements = [2, 1, 0];

            top_down(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn multiple_swaps() {
            let mut elements = [2, 0, 3, 1];

            top_down(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }
}
