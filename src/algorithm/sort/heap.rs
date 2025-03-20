//! Implementations of [Heap Sort](https://en.wikipedia.org/wiki/Heapsort).

/// Sort `elements` via bottom-up heap sort.
///
/// # Algorithm
/// Starting from lone elements which are themselves max-heap ordered,
/// iteratively join these subtrees by sifting down the element corresponding
/// to their parent until all elements are ordered. The max element (the root)
/// can then be swapped with the leaf with the highest index thereby placing it
/// in sorted order, sifting down the leaf to maintain ordering of the heap.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(N ⋅ log N) | 𝛀(N ⋅ log N)| 𝚯(N ⋅ log N) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
///
/// # Examples
/// ```
/// use rust::algorithm::sort::heap::bottom_up;
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
/// # Algorithm
/// The implementation of [`bottom_up`] first creates a max-heap, and then
/// separately uses that structure to obtain elements in sorted order thereby
/// having two independent execution paths which ultimately invoke
/// `sift_down`. In contrast, this implementation combines both steps with
/// one shared execution path which would likely result in different runtime
/// characteristics given branch prediction and potential inline expansion.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(N ⋅ log N) | 𝛀(N ⋅ log N)| 𝚯(N ⋅ log N) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
///
/// # Examples
/// ```
/// use rust::algorithm::sort::heap::inline;
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
    // into sorted order. This implies `unsorted..` are sorted.
    let mut unsorted = elements.len();

    while unsorted > 1 {
        // The heap has yet to be constructed, and this iteration will
        // sift down the new root at index `heap` into the existing heap.
        if root > 0 {
            if let Some(decremented) = root.checked_sub(1) {
                root = decremented;
            } else {
                unreachable!("outer if ensures `root > 0`");
            }
        }
        // The heap has been constructed, hence `elements[0]` is the max
        // element which can therefore be swapped into sorted order, and
        // this iteration will sift down the leaf swapped with the root.
        else {
            if let Some(decremented) = unsorted.checked_sub(1) {
                unsorted = decremented;
            } else {
                unreachable!("the loop exits when the variable becomes zero");
            }

            elements.swap(unsorted, 0);
        }

        let Some(heap) = elements.get_mut(root..unsorted) else {
            unreachable!("loop ensures both are within bounds");
        };

        sift_down::top_down(heap);
    }
}

/// Sort `elements` via top-down heap sort.
///
/// # Algorithm
/// In contrast to [`bottom_up`] which creates many small max-heaps from the
/// leaves and then joins them together via sift-down, this creates only one
/// max-heap containing the first element then iteratively adding the adjacent
/// element as a leaf and sifting it up. Once all elements are in max-heap
/// order, the overall max element (the root) can then be swapped with the leaf
/// with the highest index thereby placing it in sorted order, sifting down the
/// leaf to maintain ordering of the heap.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(N ⋅ log N) | 𝛀(N ⋅ log N)| 𝚯(N ⋅ log N) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
///
/// # Examples
/// ```
/// use rust::algorithm::sort::heap::top_down;
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

/// Index of the left child of the node at `root` in a binary heap.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1)| 𝚯(1) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
#[inline]
fn left_child(root: usize) -> Option<usize> {
    root.checked_mul(2).and_then(|index| index.checked_add(1))
}

/// Index of the right child of the node at `root` in a binary heap.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1)| 𝚯(1) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
#[inline]
fn right_child(root: usize) -> Option<usize> {
    root.checked_mul(2).and_then(|index| index.checked_add(2))
}

/// Index of the parent of the node at `child` in a binary heap.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1)| 𝚯(1) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
#[inline]
fn parent(child: usize) -> Option<usize> {
    child.checked_sub(1).map(|index| index / 2)
}

/// Sift the last leaf of a `max_heap` up to the correct position.
///
/// # Algorithm
/// Swap the leaf with its parent until the parent is greater.
///
/// # Performance
/// #### Time Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(log N) | 𝛀(log N)| 𝚯(log N) |
///
/// #### Memory Complexity
/// | Worst | Best | Average |
/// | :-: | :-: | :-: |
/// | O(1) | 𝛀(1) | 𝚯(1) |
fn sift_up<T: Ord>(max_heap: &mut [T]) {
    let Some(mut current) = max_heap.len().checked_sub(1) else {
        debug_assert!(max_heap.is_empty(), "only condition it is none");
        return;
    };

    while current > 0 {
        let Some(parent) = parent(current) else {
            unreachable!("`current > 0` => is not root => has parent");
        };

        if max_heap.get(parent) < max_heap.get(current) {
            max_heap.swap(current, parent);
            current = parent;
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
    /// # Algorithm
    /// Swap the current root with its greatest child until both its children
    /// are less than it, thereby repairing the max-heap.
    ///
    /// # Performance
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(log N) | 𝛀(log N)| 𝚯(log N) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    pub(super) fn top_down<T: Ord>(max_heap: &mut [T]) {
        let mut root = 0;

        loop {
            let (Some(left_child), Some(right_child)) =
                (left_child(root), right_child(root))
            else {
                unreachable!("loop prevents a root without children");
            };

            let child = match (max_heap.get(left_child), max_heap.get(right_child)) {
                (Some(left), Some(right)) => {
                    if left < right {
                        right_child
                    } else {
                        left_child
                    }
                }
                (Some(_), None) => left_child,
                (None, Some(_)) => unreachable!("left has smaller index"),
                (None, None) => break,
            };

            if max_heap.get(root) < max_heap.get(child) {
                max_heap.swap(root, child);
                root = child;
            } else {
                break;
            }
        }
    }

    /// Sift the root of a binary `max_heap` down to the correct position.
    ///
    /// # Algorithm
    /// Traverse the heap down to the lead with the overall smallest value
    /// (this is presumably where the current root value came from), and then
    /// traverse upwards until a node is found which is greater than the value
    /// being sifted down.
    ///
    /// This uses fewer comparison than [`top_down`], but will likely have
    /// worse performance for cheap comparisons.
    ///
    /// # Performance
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(log N) | 𝛀(log N)| 𝚯(log N) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    pub(super) fn bottom_up<T: Ord>(max_heap: &mut [T]) {
        let mut current = 0;

        // Traverse down to leaf where the smallest possible value goes.
        loop {
            let (Some(left_child), Some(right_child)) = (left_child(current), right_child(current))
            else {
                unreachable!("loop ensures current is internal node with children");
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
            if max_heap.first() > max_heap.get(current) {
                let Some(parent) = parent(current) else {
                    unreachable!("`root != 0` => not overall root => has children");
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
                unreachable!("`root != 0` => not overall root => has children");
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
mod test {
    use super::*;

    mod bottom_up {
        use super::*;

        #[test]
        fn handles_when_input_is_empty() {
            let mut elements: [usize; 0] = [];

            bottom_up(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn handles_when_input_is_single_element() {
            let mut elements = [0];

            bottom_up(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn does_not_modify_input_when_already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            debug_assert!(elements.is_sorted());

            bottom_up(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn will_swap_elements_if_in_decreasing_order() {
            let mut elements = [1, 0];

            bottom_up(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_odd_length() {
            let mut elements = [2, 1, 0];

            bottom_up(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_even_length() {
            let mut elements = [2, 0, 3, 1];

            bottom_up(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod inline {
        use super::*;

        #[test]
        fn handles_when_input_is_empty() {
            let mut elements: [usize; 0] = [];

            inline(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn handles_when_input_is_single_element() {
            let mut elements = [0];

            inline(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn does_not_modify_input_when_already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            debug_assert!(elements.is_sorted());

            inline(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn will_swap_elements_if_in_decreasing_order() {
            let mut elements = [1, 0];

            inline(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_odd_length() {
            let mut elements = [2, 1, 0];

            inline(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_even_length() {
            let mut elements = [2, 0, 3, 1];

            inline(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }

    mod top_down {
        use super::*;

        #[test]
        fn handles_when_input_is_empty() {
            let mut elements: [usize; 0] = [];

            top_down(&mut elements);

            assert_eq!(elements, []);
        }

        #[test]
        fn handles_when_input_is_single_element() {
            let mut elements = [0];

            top_down(&mut elements);

            assert_eq!(elements, [0]);
        }

        #[test]
        fn does_not_modify_input_when_already_sorted() {
            let mut elements = [0, 1, 2, 3, 4, 5];
            debug_assert!(elements.is_sorted());

            top_down(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3, 4, 5]);
        }

        #[test]
        fn will_swap_elements_if_in_decreasing_order() {
            let mut elements = [1, 0];

            top_down(&mut elements);

            assert_eq!(elements, [0, 1]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_odd_length() {
            let mut elements = [2, 1, 0];

            top_down(&mut elements);

            assert_eq!(elements, [0, 1, 2]);
        }

        #[test]
        fn correctly_orders_elements_when_input_has_even_length() {
            let mut elements = [2, 0, 3, 1];

            top_down(&mut elements);

            assert_eq!(elements, [0, 1, 2, 3]);
        }
    }
}
