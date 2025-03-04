//! Implementation of [`AdelsonVelskyLandis`].

extern crate alloc;

use super::Collection;
use super::Graph;
use super::Directed;
use super::RootedTree;

/// A self-balancing binary search tree.
///
/// Unlike an unbalanced binary search tree, the heights of the two child
/// subtrees of any [`Node`] differ by at most one thereby minimizing the
/// height of the overall tree and providing optimal lookup/search performance.
///
/// See Also: [Wikipedia](https://en.wikipedia.org/wiki/AVL_tree).
pub struct AdelsonVelskyLandis<T> {
    /// The [`Node`] that is defined as the root.
    root: Option<core::ptr::NonNull<Node<T>>>,
}

impl<T: Ord> AdelsonVelskyLandis<T> {
    /// Move an `element` into [`Self`].
    ///
    /// # Errors
    /// Yields the `element` and a reference to the corresponding equivalent
    /// value if it already exists within [`Self`].
    ///
    /// # Panics
    /// The Rust runtime might abort if allocation fails, panics otherwise.
    ///
    /// # Performance
    /// This method takes O(log N) times and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::graph::rooted_tree::AdelsonVelskyLandis;
    ///
    /// let mut instance = AdelsonVelskyLandis::default();
    ///
    /// // Ok with reference to inserted when not already contained.
    /// assert_eq!(instance.insert(0), Ok(&0));
    ///
    /// // Err with element and reference to existing when already contained.
    /// assert_eq!(instance.insert(0), Err((0, &0)));
    /// ```
    pub fn insert(&mut self, element: T) -> Result<&T, (T, &T)> {
        // Insert the element as if a non-balancing binary search tree.
        let (mut current, mut previous) = {
            let mut parent = None;
            let mut branch = &mut self.root;

            while let &mut Some(mut node) = branch {
                parent = Some(node);

                // SAFETY: no other reference to this node exists to alias.
                let node = unsafe { node.as_mut() };

                branch = match element.cmp(&node.element) {
                    core::cmp::Ordering::Less => &mut node.left,
                    core::cmp::Ordering::Greater => &mut node.right,
                    core::cmp::Ordering::Equal => return Err((element, &node.element)),
                }
            }

            let Some(new) = core::ptr::NonNull::new(Box::into_raw(Box::new(Node {
                element,
                parent,
                balance: BalanceFactor::Balanced,
                left: None,
                right: None,
            }))) else {
                unreachable!("Box panics if allocation fails, hence not null");
            };

            (parent, *branch.insert(new))
        };

        let inserted = previous;

        // Ascend ancestors of the inserted element to find unbalanced node.
        while let Some(mut ancestor) = current {
            // SAFETY: no other reference to this node exists to alias.
            if unsafe { ancestor.as_ref() }.left.is_some_and(|left| left == previous) {
                // Ascended via the left branch.

                // SAFETY: no other reference to this node exists to alias.
                let Some(child) = unsafe { ancestor.as_ref() }.left else {
                    unreachable!("ascended via the left branch");
                };

                // SAFETY: no other reference to this node exists to alias.
                match unsafe { ancestor.as_ref() }.balance {
                    BalanceFactor::Left => {
                        // Inserted into left branch, but it was was already
                        // longer than the right branch, so rotation needed.

                        // SAFETY: no other reference to this node exists to alias.
                        if unsafe { child.as_ref() }.balance == BalanceFactor::Right {
                            // SAFETY: no other reference to this node exists to alias.
                            unsafe { ancestor.as_mut() }.left = Some(Node::rotate_left(child));
                        }

                        // SAFETY: no other reference to this node exists to alias.
                        let branch = if let Some(mut parent) = unsafe { ancestor.as_ref() }.parent {
                            // SAFETY: no other reference to this node exists to alias.
                            let parent = unsafe { parent.as_mut() };

                            if parent.left.is_some_and(|left| left == ancestor) {
                                // Ancestor is the left child of its parent.
                                &mut parent.left
                            } else {
                                // Ancestor is the left child of its parent.
                                &mut parent.right
                            }
                        } else {
                            &mut self.root
                        };

                        *branch = Some(Node::rotate_right(ancestor));

                        // The rotation balanced the tree.
                        break;
                    },
                    BalanceFactor::Right => {
                        // Inserted into left branch, but the right branch was
                        // the longer branch, so now both are balanced.

                        // SAFETY: no other reference to this node exists to alias.
                        unsafe{ ancestor.as_mut() }.balance = BalanceFactor::Balanced;

                        // Further ancestors retain existing balance factors.
                        break;
                    },
                    BalanceFactor::Balanced => {
                        // Inserted into the left branch, but both branches
                        // were equal length, so only rotating a higher
                        // ancestor could equalize their heights.

                        // SAFETY: no other reference to this node exists to alias.
                        unsafe{ ancestor.as_mut() }.balance = BalanceFactor::Left;
                    },
                }
            } else {
                // Ascended via the right branch.

                // SAFETY: no other reference to this node exists to alias.
                let Some(child) = unsafe { ancestor.as_ref() }.right else {
                    unreachable!("ascended via the right branch");
                };

                // SAFETY: no other reference to this node exists to alias.
                match unsafe { ancestor.as_ref() }.balance {
                    BalanceFactor::Left => {
                        // Inserted into right branch, but the left branch was
                        // the longer branch, so now both are balanced.

                        // SAFETY: no other reference to this node exists to alias.
                        unsafe{ ancestor.as_mut() }.balance = BalanceFactor::Balanced;

                        // Further ancestors retain existing balance factors.
                        break;
                    },
                    BalanceFactor::Right => {
                        // Inserted into right branch, but it was was already
                        // longer than the left branch, so rotation needed.

                        // SAFETY: no other reference to this node exists to alias.
                        if unsafe { child.as_ref() }.balance == BalanceFactor::Left {
                            // SAFETY: no other reference to this node exists to alias.
                            unsafe { ancestor.as_mut() }.right = Some(Node::rotate_right(child));
                        }

                        // SAFETY: no other reference to this node exists to alias.
                        let branch = if let Some(mut parent) = unsafe { ancestor.as_ref() }.parent {
                            // SAFETY: no other reference to this node exists to alias.
                            let parent = unsafe { parent.as_mut() };

                            if parent.left.is_some_and(|left| left == ancestor) {
                                // Ancestor is the left child of its parent.
                                &mut parent.left
                            } else {
                                // Ancestor is the left child of its parent.
                                &mut parent.right
                            }
                        } else {
                            &mut self.root
                        };

                        *branch = Some(Node::rotate_left(ancestor));

                        // The rotation balanced the tree.
                        break;
                    },
                    BalanceFactor::Balanced => {
                        // Inserted into the right branch, but both branches
                        // were equal length, so only rotating a higher
                        // ancestor could equalize their heights.

                        // SAFETY: no other reference to this node exists to alias.
                        unsafe{ ancestor.as_mut() }.balance = BalanceFactor::Right;
                    },
                }
            }

            previous = ancestor;

            // SAFETY: no other reference to this node exists to alias.
            current = unsafe { ancestor.as_ref() }.parent;
        }

        // SAFETY: no other reference to this node exists to alias.
        Ok(&unsafe { inserted.as_ref() }.element)
    }

    /// Move the element with value `element` out of [`Self`], if it exists.
    ///
    /// # Performance
    /// This method takes O(log N) times and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::graph::rooted_tree::AdelsonVelskyLandis;
    ///
    /// let mut instance = AdelsonVelskyLandis::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// // None when not contained.
    /// assert_eq!(instance.remove(&6), None);
    ///
    /// // Some when contained.
    /// assert_eq!(instance.remove(&1), Some(1));
    /// ```
    #[allow(clippy::too_many_lines)]
    pub fn remove(&mut self, element: &T) -> Option<T> {
        // STEP 1: Find the element to be removed and its parent.
        let (parent, removing) = {
            let mut parent = None;
            let mut branch = &mut self.root;

            while let &mut Some(mut next) = branch {
                // SAFETY: no other reference to this node exists to alias.
                let node = unsafe { next.as_mut() };

                branch = match element.cmp(&node.element) {
                    core::cmp::Ordering::Less => &mut node.left,
                    core::cmp::Ordering::Greater => &mut node.right,
                    core::cmp::Ordering::Equal => break,
                };

                parent = Some(next);
            }

            (parent, (*branch)?)
        };

        // STEP 2: Handle special case of removing having both children.
        let (parent, removing) = {
            let mut parent = parent;
            let mut removing = removing;

            // SAFETY: no other reference to this node exists to alias.
            let root = unsafe { removing.as_mut() };

            // Swap removing's element with its in-order successor's.
            if let (Some(_left), Some(right)) = (root.left, root.right) {
                // Descend down the right branch, then find leftmost descendant.
                parent = Some(removing);
                removing = right;

                // SAFETY: no other reference to this node exists to alias.
                while let Some(successor) = unsafe { removing.as_ref() }.left {
                    parent = Some(removing);
                    removing = successor;
                }

                // SAFETY: no other reference to this node exists to alias.
                let successor = unsafe { removing.as_mut() };

                core::mem::swap(&mut root.element, &mut successor.element);
            }

            (parent, removing)
        };

        // STEP 3: Ascend ancestors of the removed element to find imbalance.
        #[allow(clippy::shadow_unrelated)]
        #[allow(clippy::redundant_closure_call)]
        (|mut parent: Option<core::ptr::NonNull<Node<T>>>, mut removing: core::ptr::NonNull<Node<T>>| {
            while let Some(mut ancestor) = parent {
                // SAFETY: no other reference to this node exists to alias.
                if unsafe { ancestor.as_ref() }.left.is_some_and(|left| left == removing) {
                    // Ascended via the left branch.

                    // SAFETY: no other reference to this node exists to alias.
                    match unsafe { ancestor.as_ref() }.balance {
                        BalanceFactor::Left => {
                            // Removed from left branch, but the left branch was
                            // the longer branch, so now both are balanced.

                            // SAFETY: no other reference to this node exists to alias.
                            unsafe { ancestor.as_mut() }.balance = BalanceFactor::Balanced;
                        },
                        BalanceFactor::Right => {
                            // Removed from left branch, but the right
                            // branch was already longer than the left
                            // branch, so rotation needed.

                            // SAFETY: no other reference to this node exists to alias.
                            let Some(child) = unsafe { ancestor.as_ref() }.right else {
                                unreachable!("balanced right implies existence of right child");
                            };

                            // SAFETY: no other reference to this node exists to alias.
                            if unsafe { child.as_ref() }.balance == BalanceFactor::Left {
                                // SAFETY: no other reference to this node exists to alias.
                                unsafe { ancestor.as_mut() }.right = Some(Node::rotate_right(child));
                            }

                            // SAFETY: no other reference to this node exists to alias.
                            let branch = if let Some(mut grand_parent) = unsafe { ancestor.as_ref() }.parent {
                                // SAFETY: no other reference to this node exists to alias.
                                let grand_parent = unsafe { grand_parent.as_mut() };

                                if grand_parent.left.is_some_and(|left| left == ancestor) {
                                    // Ancestor is the left child of its parent.
                                    &mut grand_parent.left
                                } else {
                                    // Ancestor is the left child of its parent.
                                    &mut grand_parent.right
                                }
                            } else {
                                &mut self.root
                            };

                            *branch = Some(Node::rotate_left(ancestor));

                            // The rotation balanced the tree.
                            break;
                        },
                        BalanceFactor::Balanced => {
                            // Removed from left branch, but both branches were
                            // equal length, so now the right branch is longer.

                            // SAFETY: no other reference to this node exists to alias.
                            unsafe { ancestor.as_mut() }.balance = BalanceFactor::Right;

                            break;
                        },
                    }
                } else {
                    // Ascended via the right branch.

                    // SAFETY: no other reference to this node exists to alias.
                    match unsafe { ancestor.as_ref() }.balance {
                        BalanceFactor::Left => {
                            // Removed from right branch, but the left
                            // branch was already longer than the right
                            // branch, so rotation needed.

                            // SAFETY: no other reference to this node exists to alias.
                            let Some(child) = unsafe { ancestor.as_ref() }.left else {
                                unreachable!("balanced left implies existence of left child");
                            };

                            // SAFETY: no other reference to this node exists to alias.
                            if unsafe { child.as_ref() }.balance == BalanceFactor::Right {
                                // SAFETY: no other reference to this node exists to alias.
                                unsafe { ancestor.as_mut() }.left = Some(Node::rotate_left(child));
                            }

                            // SAFETY: no other reference to this node exists to alias.
                            let branch = if let Some(mut grand_parent) = unsafe { ancestor.as_ref() }.parent {
                                // SAFETY: no other reference to this node exists to alias.
                                let grand_parent = unsafe { grand_parent.as_mut() };

                                if grand_parent.left.is_some_and(|left| left == ancestor) {
                                    // Ancestor is the left child of its parent.
                                    &mut grand_parent.left
                                } else {
                                    // Ancestor is the left child of its parent.
                                    &mut grand_parent.right
                                }
                            } else {
                                &mut self.root
                            };

                            *branch = Some(Node::rotate_right(ancestor));

                            // The rotation balanced the tree.
                            break;
                        },
                        BalanceFactor::Right => {
                            // Removed from right branch, but the right branch was
                            // the longer branch, so now both are balanced.

                            // SAFETY: no other reference to this node exists to alias.
                            unsafe { ancestor.as_mut() }.balance = BalanceFactor::Balanced;
                        },
                        BalanceFactor::Balanced => {
                            // Removed from right branch, but both branches were
                            // equal length, so now the left branch is longer.

                            // SAFETY: no other reference to this node exists to alias.
                            unsafe { ancestor.as_mut() }.balance = BalanceFactor::Left;

                            break;
                        },
                    }
                }

                removing = ancestor;

                // SAFETY: no other reference to this node exists to alias.
                parent = unsafe { ancestor.as_ref() }.parent;
            }
        }) (parent, removing);

        // STEP 4: Actually remove the node.
        let removed = {
            // SAFETY:
            // * Constructed via `Box::to_inner`.
            // * The following removes the pointer so it will be inaccessible.
            let mut removed = unsafe { Box::from_raw(removing.as_ptr()) };

            // Owning pointer to the removed node.
            let branch = if let Some(mut grand_parent) = parent {
                // SAFETY: no other reference to this node exists to alias.
                let grand_parent = unsafe { grand_parent.as_mut() };

                if grand_parent.left.is_some_and(|left| left == removing) {
                    // Removed is the left child of its parent.
                    &mut grand_parent.left
                } else {
                    // Removed is the left child of its parent.
                    &mut grand_parent.right
                }
            } else {
                &mut self.root
            };

            // Connect parent to the child of the removed node.
            *branch = match (removed.left.take(), removed.right.take()) {
                (None, None) => None,
                (Some(mut child), None) | (None, Some(mut child)) => {
                    // SAFETY: no other reference to this node exists to alias.
                    let node = unsafe { child.as_mut() };

                    node.parent = removed.parent.take();

                    Some(child)
                },
                (Some(_), Some(_)) => {
                    unreachable!("step 2 already handled this special case");
                }
            };

            removed.element
        };

        Some(removed)
    }
}

impl<T> Default for AdelsonVelskyLandis<T> {
    /// Construct an empty instance.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::graph::rooted_tree::AdelsonVelskyLandis;
    ///
    /// let instance = AdelsonVelskyLandis::default();
    ///
    /// todo!("show that it is empty");
    /// ```
    fn default() -> Self {
        Self { root: None }
    }
}

impl<T: Ord> FromIterator<T> for AdelsonVelskyLandis<T> {
    /// Construct by moving elements from an iterator.
    ///
    /// Elements are inserted in order, later duplicates being dropped.
    ///
    /// # Panics
    /// The Rust runtime might abort if allocation fails, panics otherwise.
    ///
    /// # Performance
    /// This methods takes O(N * log(N)) time and consumes O(N) memory for the
    /// result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::graph::rooted_tree::AdelsonVelskyLandis;
    ///
    /// let instance = AdelsonVelskyLandis::from_iter(1..=5);
    ///
    /// todo!("show that it contains those elements in that order");
    /// ```
    fn from_iter<Iter: IntoIterator<Item = T>>(iter: Iter) -> Self {
        let mut instance = AdelsonVelskyLandis::default();

        for element in iter {
            drop(instance.insert(element));
        }

        instance
    }
}

/// Which branch of a [`Node`] has the subtree with the greatest height.
#[derive(PartialEq, Eq, Debug)]
enum BalanceFactor {
    /// Both branches of this [`Node`] have the same height.
    Balanced,

    /// The left branch of this [`Node`] has height one longer than the right.
    Left,

    /// The right branch of this [`Node`] has height one longer than the left.
    Right,
}

/// An instantiated element within a [`AdelsonVelskyLandis`].
struct Node<T> {
    /// The underlying element.
    element: T,

    /// Which branch has the subtree with the greatest height.
    balance: BalanceFactor,

    /// The [`Node`] for whom this is the left or right child.
    parent: Option<core::ptr::NonNull<Node<T>>>,

    /// The left child, if any.
    left: Option<core::ptr::NonNull<Node<T>>>,

    /// The right child, if any.
    right: Option<core::ptr::NonNull<Node<T>>>,
}

impl<T: Ord> Node<T> {
    /// Perform a left rotation about the `root` of a subtree.
    ///
    /// This function will alter the structure of a subtree such that the
    /// right child will become the root maintaining AVL invariants.
    ///
    /// # Panics
    /// This method panics if `root` has no right child.
    ///
    /// # Performance
    /// This method takes O(1) times and consumes O(1) memory.
    fn rotate_left(mut root: core::ptr::NonNull<Self>) -> core::ptr::NonNull<Self> {
        // SAFETY: no other reference to this node exists to alias.
        let root_node = unsafe { root.as_mut() };

        let Some(mut right_ptr) = root_node.right.take() else {
            panic!("it is a logic error to rotate left without a right child");
        };

        // SAFETY: no other reference to this node exists to alias.
        let right_node = unsafe { right_ptr.as_mut() };

        if let Some(mut right_left_ptr) = right_node.left.take() {
            // SAFETY: no other reference to this node exists to alias.
            let right_left_node = unsafe { right_left_ptr.as_mut() };

            right_left_node.parent = Some(root);
            root_node.right = Some(right_left_ptr);
        }

        right_node.parent = root_node.parent.replace(right_ptr);

        right_node.left = Some(root);

        right_node.balance = match (right_node.left, right_node.right) {
            (Some(_), Some(_)) => BalanceFactor::Balanced,
            (Some(_), None) => BalanceFactor::Left,
            (None, None | Some(_)) => unreachable!("left child was assigned to be root"),
        };

        root_node.balance = match (root_node.left, root_node.right) {
            (Some(_), Some(_)) | (None, None) => BalanceFactor::Balanced,
            (Some(_), None) => BalanceFactor::Left,
            (None, Some(_)) => BalanceFactor::Right,
        };

        right_ptr
    }

    /// Perform a right rotation about the `root` of a subtree.
    ///
    /// This function will alter the structure of a subtree such that the
    /// left child will become the root maintaining AVL invariants.
    ///
    /// # Panics
    /// This method panics if `root` has no left child.
    ///
    /// # Performance
    /// This method takes O(1) times and consumes O(1) memory.
    fn rotate_right(mut root: core::ptr::NonNull<Self>) -> core::ptr::NonNull<Self> {
        // SAFETY: no other reference to this node exists to alias.
        let root_node = unsafe { root.as_mut() };

        let Some(mut left_ptr) = root_node.left.take() else {
            panic!("it is a logic error to rotate left without a right child");
        };

        // SAFETY: no other reference to this node exists to alias.
        let left_node = unsafe { left_ptr.as_mut() };

        if let Some(mut left_right) = left_node.right.take() {
            // SAFETY: no other reference to this node exists to alias.
            let left_right_node = unsafe { left_right.as_mut() };

            left_right_node.parent = Some(root);
            root_node.left = Some(left_right);
        }

        left_node.parent = root_node.parent.replace(left_ptr);

        left_node.right = Some(root);

        left_node.balance = match (left_node.left, left_node.right) {
            (Some(_), Some(_)) => BalanceFactor::Balanced,
            (None, Some(_)) => BalanceFactor::Right,
            (None | Some(_), None) => unreachable!("right child was assigned to be root"),
        };

        root_node.balance = match (root_node.left, root_node.right) {
            (Some(_), Some(_)) | (None, None) => BalanceFactor::Balanced,
            (Some(_), None) => BalanceFactor::Left,
            (None, Some(_)) => BalanceFactor::Right,
        };

        left_ptr
    }
}

#[cfg(test)]
#[allow(
    clippy::undocumented_unsafe_blocks,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::assertions_on_result_states
)]
mod test {
    use super::*;

    mod method {
        use super::*;

        mod insert {
            use super::*;

            #[test]
            fn when_empty() {
                let mut instance = AdelsonVelskyLandis::<i32>::default();

                assert!(instance.insert(0).is_ok());

                // SAFETY: no other reference exists to this node to alias.
                let root = unsafe { instance.root.unwrap().as_ref() };

                assert_eq!(root.element, 0);
                assert_eq!(root.balance, BalanceFactor::Balanced);
                assert_eq!(root.parent, None);
                assert!(root.left.is_none());
                assert!(root.right.is_none());
            }

            #[test]
            fn yields_element_when_not_contained() {
                let mut instance = AdelsonVelskyLandis::default();

                for element in 0..=5 {
                    assert_eq!(instance.insert(element), Ok(&element));
                }
            }

            #[test]
            fn yields_error_when_already_contained() {
                let elements = 0..8;

                #[allow(clippy::from_iter_instead_of_collect)]
                let mut instance = AdelsonVelskyLandis::from_iter(elements.clone());

                for element in elements {
                    assert!(instance.insert(element).is_err());
                }
            }

            mod does_no_rotation {
                use super::*;

                mod when_extending_root {
                    use super::*;

                    mod when_leaf_is_left_child {
                        use super::*;

                        /// Should create the following structure:
                        ///
                        /// ```
                        ///   2
                        ///  / \
                        /// 1
                        /// ```
                        ///
                        /// The final insertion of element '1' should invoke
                        /// no rotation therefore remaining the same structure.
                        fn setup() -> AdelsonVelskyLandis<usize> {
                            let mut instance = AdelsonVelskyLandis::default();

                            assert!(instance.insert(2).is_ok());
                            assert!(instance.insert(1).is_ok());

                            instance
                        }

                        #[test]
                        fn root() {
                            let instance = setup();

                            // SAFETY: no other reference exists to this node to alias.
                            let root = unsafe { instance.root.unwrap().as_ref() };

                            assert_eq!(root.element, 2);
                            assert_eq!(root.balance, BalanceFactor::Left);
                            assert_eq!(root.parent, None);
                            assert!(root.left.is_some());
                            assert!(root.right.is_none());
                        }

                        #[test]
                        fn left_child() {
                            let instance = setup();

                            let root_ptr = instance.root.unwrap();

                            // SAFETY: no other reference exists to this node to alias.
                            let root = unsafe { root_ptr.as_ref() };

                            // SAFETY: no other reference exists to this node to alias.
                            let left = unsafe { root.left.unwrap().as_ref() };

                            assert_eq!(left.element, 1);
                            assert_eq!(left.balance, BalanceFactor::Balanced);
                            assert_eq!(left.parent, Some(root_ptr));
                            assert!(left.left.is_none());
                            assert!(left.right.is_none());
                        }
                    }

                    mod when_leaf_is_right_child {
                        use super::*;

                        /// Should create the following structure:
                        ///
                        /// ```
                        ///   1
                        ///  / \
                        ///    2
                        /// ```
                        ///
                        /// The final insertion of element '2' should invoke
                        /// no rotation therefore remaining the same structure.
                        fn setup() -> AdelsonVelskyLandis<usize> {
                            let mut instance = AdelsonVelskyLandis::default();

                            assert!(instance.insert(1).is_ok());
                            assert!(instance.insert(2).is_ok());

                            instance
                        }

                        #[test]
                        fn root() {
                            let instance = setup();

                            // SAFETY: no other reference exists to this node to alias.
                            let root = unsafe { instance.root.unwrap().as_ref() };

                            assert_eq!(root.element, 1);
                            assert_eq!(root.balance, BalanceFactor::Right);
                            assert_eq!(root.parent, None);
                            assert!(root.left.is_none());
                            assert!(root.right.is_some());
                        }

                        #[test]
                        fn right_child() {
                            let instance = setup();

                            let root_ptr = instance.root.unwrap();

                            // SAFETY: no other reference exists to this node to alias.
                            let root = unsafe { root_ptr.as_ref() };

                            // SAFETY: no other reference exists to this node to alias.
                            let right = unsafe { root.right.unwrap().as_ref() };

                            assert_eq!(right.element, 2);
                            assert_eq!(right.balance, BalanceFactor::Balanced);
                            assert_eq!(right.parent, Some(root_ptr));
                            assert!(right.left.is_none());
                            assert!(right.right.is_none());
                        }
                    }
                }

                mod when_creates_single_imbalance {
                    use super::*;

                    mod to_the_left {
                        use super::*;

                        mod when_leaf_is_left_child {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///     3
                            ///    / \
                            ///   2  4
                            ///  / \
                            /// 1
                            /// ```
                            ///
                            /// The final insertion of element '1' should
                            /// invoke no rotation therefore remaining the
                            /// same structure.
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(3).is_ok());

                                assert!(instance.insert(2).is_ok());
                                assert!(instance.insert(4).is_ok());

                                assert!(instance.insert(1).is_ok());

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 3);
                                assert_eq!(root.balance, BalanceFactor::Left);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_some());
                            }

                            #[test]
                            fn left_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 2);
                                assert_eq!(left.balance, BalanceFactor::Left);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_some());
                                assert!(left.right.is_none());
                            }

                            #[test]
                            fn left_left_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let left_ptr = root.left.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { left_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left_left = unsafe { left.left.unwrap().as_ref() };

                                assert_eq!(left_left.element, 1);
                                assert_eq!(left_left.balance, BalanceFactor::Balanced);
                                assert_eq!(left_left.parent, Some(left_ptr));
                                assert!(left_left.left.is_none());
                                assert!(left_left.right.is_none());
                            }

                            #[test]
                            fn right_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { root.right.unwrap().as_ref() };

                                assert_eq!(right.element, 4);
                                assert_eq!(right.balance, BalanceFactor::Balanced);
                                assert_eq!(right.parent, Some(root_ptr));
                                assert!(right.left.is_none());
                                assert!(right.right.is_none());
                            }
                        }

                        mod when_leaf_is_right_child {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///    3
                            ///   / \
                            ///  1  4
                            /// / \
                            ///   2
                            /// ```
                            ///
                            /// The final insertion of element '2' should
                            /// invoke no rotation therefore remaining the
                            /// same structure.
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(3).is_ok());

                                assert!(instance.insert(1).is_ok());
                                assert!(instance.insert(4).is_ok());

                                assert!(instance.insert(2).is_ok());

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 3);
                                assert_eq!(root.balance, BalanceFactor::Left);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_some());
                            }

                            #[test]
                            fn left_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 1);
                                assert_eq!(left.balance, BalanceFactor::Right);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_none());
                                assert!(left.right.is_some());
                            }

                            #[test]
                            fn left_right_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let left_ptr = root.left.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { left_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left_right = unsafe { left.right.unwrap().as_ref() };

                                assert_eq!(left_right.element, 2);
                                assert_eq!(left_right.balance, BalanceFactor::Balanced);
                                assert_eq!(left_right.parent, Some(left_ptr));
                                assert!(left_right.left.is_none());
                                assert!(left_right.right.is_none());
                            }

                            #[test]
                            fn right_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { root.right.unwrap().as_ref() };

                                assert_eq!(right.element, 4);
                                assert_eq!(right.balance, BalanceFactor::Balanced);
                                assert_eq!(right.parent, Some(root_ptr));
                                assert!(right.left.is_none());
                                assert!(right.right.is_none());
                            }
                        }
                    }

                    mod to_the_right {
                        use super::*;

                        mod when_leaf_is_left_child {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///   2
                            ///  / \
                            /// 1  4
                            ///   / \
                            ///  3
                            /// ```
                            ///
                            /// The final insertion of element '3' should
                            /// invoke no rotation therefore remaining the
                            /// same structure.
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(2).is_ok());

                                assert!(instance.insert(1).is_ok());
                                assert!(instance.insert(4).is_ok());

                                assert!(instance.insert(3).is_ok());

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 2);
                                assert_eq!(root.balance, BalanceFactor::Right);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_some());
                            }

                            #[test]
                            fn left_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 1);
                                assert_eq!(left.balance, BalanceFactor::Balanced);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_none());
                                assert!(left.right.is_none());
                            }

                            #[test]
                            fn right_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { root.right.unwrap().as_ref() };

                                assert_eq!(right.element, 4);
                                assert_eq!(right.balance, BalanceFactor::Left);
                                assert_eq!(right.parent, Some(root_ptr));
                                assert!(right.left.is_some());
                                assert!(right.right.is_none());
                            }

                            #[test]
                            fn right_left_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let right_ptr = root.right.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { right_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right_left = unsafe { right.left.unwrap().as_ref() };

                                assert_eq!(right_left.element, 3);
                                assert_eq!(right_left.balance, BalanceFactor::Balanced);
                                assert_eq!(right_left.parent, Some(right_ptr));
                                assert!(right_left.left.is_none());
                                assert!(right_left.right.is_none());
                            }
                        }

                        mod when_leaf_is_right_child {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///   2
                            ///  / \
                            /// 1  3
                            ///   / \
                            ///     4
                            /// ```
                            ///
                            /// The final insertion of element '4' should
                            /// invoke no rotation therefore remaining the
                            /// same structure.
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(2).is_ok());

                                assert!(instance.insert(1).is_ok());
                                assert!(instance.insert(3).is_ok());

                                assert!(instance.insert(4).is_ok());

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 2);
                                assert_eq!(root.balance, BalanceFactor::Right);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_some());
                            }

                            #[test]
                            fn left_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 1);
                                assert_eq!(left.balance, BalanceFactor::Balanced);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_none());
                                assert!(left.right.is_none());
                            }

                            #[test]
                            fn right_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { root.right.unwrap().as_ref() };

                                assert_eq!(right.element, 3);
                                assert_eq!(right.balance, BalanceFactor::Right);
                                assert_eq!(right.parent, Some(root_ptr));
                                assert!(right.left.is_none());
                                assert!(right.right.is_some());
                            }

                            #[test]
                            fn right_right_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let right_ptr = root.right.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { right_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right_right = unsafe { right.right.unwrap().as_ref() };

                                assert_eq!(right_right.element, 4);
                                assert_eq!(right_right.balance, BalanceFactor::Balanced);
                                assert_eq!(right_right.parent, Some(right_ptr));
                                assert!(right_right.left.is_none());
                                assert!(right_right.right.is_none());
                            }
                        }
                    }
                }

                mod when_balancing_unbalanced_tree {
                    use super::*;

                    mod left_imbalance {
                        use super::*;

                        mod when_leaf_is_left_child {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///      4
                            ///    /   \
                            ///   2    6
                            ///  / \  / \
                            /// 1  3 5
                            /// ```
                            ///
                            /// The final insertion of element '5' should
                            /// invoke no rotation therefore remaining the
                            /// same structure.
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(4).is_ok());

                                assert!(instance.insert(2).is_ok());
                                assert!(instance.insert(6).is_ok());

                                assert!(instance.insert(1).is_ok());
                                assert!(instance.insert(3).is_ok());

                                assert!(instance.insert(5).is_ok());

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 4);
                                assert_eq!(root.balance, BalanceFactor::Balanced);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_some());
                            }

                            #[test]
                            fn left_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 2);
                                assert_eq!(left.balance, BalanceFactor::Balanced);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_some());
                                assert!(left.right.is_some());
                            }

                            #[test]
                            fn left_left_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let left_ptr = root.left.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { left_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left_left = unsafe { left.left.unwrap().as_ref() };

                                assert_eq!(left_left.element, 1);
                                assert_eq!(left_left.balance, BalanceFactor::Balanced);
                                assert_eq!(left_left.parent, Some(left_ptr));
                                assert!(left_left.left.is_none());
                                assert!(left_left.right.is_none());
                            }

                            #[test]
                            fn left_right_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let left_ptr = root.left.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { left_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left_right = unsafe { left.right.unwrap().as_ref() };

                                assert_eq!(left_right.element, 3);
                                assert_eq!(left_right.balance, BalanceFactor::Balanced);
                                assert_eq!(left_right.parent, Some(left_ptr));
                                assert!(left_right.left.is_none());
                                assert!(left_right.right.is_none());
                            }

                            #[test]
                            fn right_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { root.right.unwrap().as_ref() };

                                assert_eq!(right.element, 6);
                                assert_eq!(right.balance, BalanceFactor::Left);
                                assert_eq!(right.parent, Some(root_ptr));
                                assert!(right.left.is_some());
                                assert!(right.right.is_none());
                            }

                            #[test]
                            fn right_left_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let right_ptr = root.right.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { right_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right_left = unsafe { right.left.unwrap().as_ref() };

                                assert_eq!(right_left.element, 5);
                                assert_eq!(right_left.balance, BalanceFactor::Balanced);
                                assert_eq!(right_left.parent, Some(right_ptr));
                                assert!(right_left.left.is_none());
                                assert!(right_left.right.is_none());
                            }
                        }

                        mod when_leaf_is_right_child {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///      4
                            ///    /   \
                            ///   2    5
                            ///  / \  / \
                            /// 1  3    6
                            /// ```
                            ///
                            /// The final insertion of element '6' should
                            /// invoke no rotation therefore remaining the
                            /// same structure.
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(4).is_ok());

                                assert!(instance.insert(2).is_ok());
                                assert!(instance.insert(5).is_ok());

                                assert!(instance.insert(1).is_ok());
                                assert!(instance.insert(3).is_ok());

                                assert!(instance.insert(6).is_ok());

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 4);
                                assert_eq!(root.balance, BalanceFactor::Balanced);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_some());
                            }

                            #[test]
                            fn left_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 2);
                                assert_eq!(left.balance, BalanceFactor::Balanced);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_some());
                                assert!(left.right.is_some());
                            }

                            #[test]
                            fn left_left_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let left_ptr = root.left.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { left_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left_left = unsafe { left.left.unwrap().as_ref() };

                                assert_eq!(left_left.element, 1);
                                assert_eq!(left_left.balance, BalanceFactor::Balanced);
                                assert_eq!(left_left.parent, Some(left_ptr));
                                assert!(left_left.left.is_none());
                                assert!(left_left.right.is_none());
                            }

                            #[test]
                            fn left_right_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let left_ptr = root.left.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { left_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left_right = unsafe { left.right.unwrap().as_ref() };

                                assert_eq!(left_right.element, 3);
                                assert_eq!(left_right.balance, BalanceFactor::Balanced);
                                assert_eq!(left_right.parent, Some(left_ptr));
                                assert!(left_right.left.is_none());
                                assert!(left_right.right.is_none());
                            }

                            #[test]
                            fn right_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { root.right.unwrap().as_ref() };

                                assert_eq!(right.element, 5);
                                assert_eq!(right.balance, BalanceFactor::Right);
                                assert_eq!(right.parent, Some(root_ptr));
                                assert!(right.left.is_none());
                                assert!(right.right.is_some());
                            }

                            #[test]
                            fn right_right_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let right_ptr = root.right.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { right_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right_right = unsafe { right.right.unwrap().as_ref() };

                                assert_eq!(right_right.element, 6);
                                assert_eq!(right_right.balance, BalanceFactor::Balanced);
                                assert_eq!(right_right.parent, Some(right_ptr));
                                assert!(right_right.left.is_none());
                                assert!(right_right.right.is_none());
                            }
                        }
                    }

                    mod right_imbalance {
                        use super::*;

                        mod when_leaf_is_left_child {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///      3
                            ///    /   \
                            ///   2    5
                            ///  / \  / \
                            /// 1    4  6
                            /// ```
                            ///
                            /// The final insertion of element '1' should
                            /// invoke no rotation therefore remaining the
                            /// same structure.
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(3).is_ok());

                                assert!(instance.insert(2).is_ok());
                                assert!(instance.insert(5).is_ok());

                                assert!(instance.insert(1).is_ok());

                                assert!(instance.insert(4).is_ok());
                                assert!(instance.insert(6).is_ok());

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 3);
                                assert_eq!(root.balance, BalanceFactor::Balanced);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_some());
                            }

                            #[test]
                            fn left_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 2);
                                assert_eq!(left.balance, BalanceFactor::Left);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_some());
                                assert!(left.right.is_none());
                            }

                            #[test]
                            fn left_left_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let left_ptr = root.left.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { left_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left_left = unsafe { left.left.unwrap().as_ref() };

                                assert_eq!(left_left.element, 1);
                                assert_eq!(left_left.balance, BalanceFactor::Balanced);
                                assert_eq!(left_left.parent, Some(left_ptr));
                                assert!(left_left.left.is_none());
                                assert!(left_left.right.is_none());
                            }

                            #[test]
                            fn right_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { root.right.unwrap().as_ref() };

                                assert_eq!(right.element, 5);
                                assert_eq!(right.balance, BalanceFactor::Balanced);
                                assert_eq!(right.parent, Some(root_ptr));
                                assert!(right.left.is_some());
                                assert!(right.right.is_some());
                            }

                            #[test]
                            fn right_left_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let right_ptr = root.right.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { right_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right_left = unsafe { right.left.unwrap().as_ref() };

                                assert_eq!(right_left.element, 4);
                                assert_eq!(right_left.balance, BalanceFactor::Balanced);
                                assert_eq!(right_left.parent, Some(right_ptr));
                                assert!(right_left.left.is_none());
                                assert!(right_left.right.is_none());
                            }

                            #[test]
                            fn right_right_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let right_ptr = root.right.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { right_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right_right = unsafe { right.right.unwrap().as_ref() };

                                assert_eq!(right_right.element, 6);
                                assert_eq!(right_right.balance, BalanceFactor::Balanced);
                                assert_eq!(right_right.parent, Some(right_ptr));
                                assert!(right_right.left.is_none());
                                assert!(right_right.right.is_none());
                            }
                        }

                        mod when_leaf_is_right_child {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///      3
                            ///    /   \
                            ///   1    5
                            ///  / \  / \
                            ///    2 4  6
                            /// ```
                            ///
                            /// The final insertion of element '2' should
                            /// invoke no rotation therefore remaining the
                            /// same structure.
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(3).is_ok());

                                assert!(instance.insert(1).is_ok());
                                assert!(instance.insert(5).is_ok());

                                assert!(instance.insert(2).is_ok());

                                assert!(instance.insert(4).is_ok());
                                assert!(instance.insert(6).is_ok());

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 3);
                                assert_eq!(root.balance, BalanceFactor::Balanced);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_some());
                            }

                            #[test]
                            fn left_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 1);
                                assert_eq!(left.balance, BalanceFactor::Right);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_none());
                                assert!(left.right.is_some());
                            }

                            #[test]
                            fn left_right_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let left_ptr = root.left.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { left_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left_right = unsafe { left.right.unwrap().as_ref() };

                                assert_eq!(left_right.element, 2);
                                assert_eq!(left_right.balance, BalanceFactor::Balanced);
                                assert_eq!(left_right.parent, Some(left_ptr));
                                assert!(left_right.left.is_none());
                                assert!(left_right.right.is_none());
                            }

                            #[test]
                            fn right_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { root.right.unwrap().as_ref() };

                                assert_eq!(right.element, 5);
                                assert_eq!(right.balance, BalanceFactor::Balanced);
                                assert_eq!(right.parent, Some(root_ptr));
                                assert!(right.left.is_some());
                                assert!(right.right.is_some());
                            }

                            #[test]
                            fn right_left_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let right_ptr = root.right.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { right_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right_left = unsafe { right.left.unwrap().as_ref() };

                                assert_eq!(right_left.element, 4);
                                assert_eq!(right_left.balance, BalanceFactor::Balanced);
                                assert_eq!(right_left.parent, Some(right_ptr));
                                assert!(right_left.left.is_none());
                                assert!(right_left.right.is_none());
                            }

                            #[test]
                            fn right_right_grandchild() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                let right_ptr = root.right.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { right_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right_right = unsafe { right.right.unwrap().as_ref() };

                                assert_eq!(right_right.element, 6);
                                assert_eq!(right_right.balance, BalanceFactor::Balanced);
                                assert_eq!(right_right.parent, Some(right_ptr));
                                assert!(right_right.left.is_none());
                                assert!(right_right.right.is_none());
                            }
                        }
                    }
                }
            }

            mod does_left_rotation {
                use super::*;

                mod when_leaf_is_left_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///   2
                    ///  / \
                    /// 1  4
                    ///   / \
                    ///  3  6
                    ///    / \
                    ///   5
                    /// ```
                    ///
                    /// The final insertion of element '5' should invoke a
                    /// left-rotation about element '2' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      4
                    ///    /   \
                    ///   2    6
                    ///  / \  / \
                    /// 1  3 5
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(4).is_ok());

                        assert!(instance.insert(2).is_ok());
                        assert!(instance.insert(6).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(3).is_ok());

                        assert!(instance.insert(5).is_ok());

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 4);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 2);
                        assert_eq!(left.balance, BalanceFactor::Balanced);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_some());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 1);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn left_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_right = unsafe { left.right.unwrap().as_ref() };

                        assert_eq!(left_right.element, 3);
                        assert_eq!(left_right.balance, BalanceFactor::Balanced);
                        assert_eq!(left_right.parent, Some(left_ptr));
                        assert!(left_right.left.is_none());
                        assert!(left_right.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 6);
                        assert_eq!(right.balance, BalanceFactor::Left);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_some());
                        assert!(right.right.is_none());
                    }

                    #[test]
                    fn right_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_left = unsafe { right.left.unwrap().as_ref() };

                        assert_eq!(right_left.element, 5);
                        assert_eq!(right_left.balance, BalanceFactor::Balanced);
                        assert_eq!(right_left.parent, Some(right_ptr));
                        assert!(right_left.left.is_none());
                        assert!(right_left.right.is_none());
                    }
                }

                mod when_leaf_is_right_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///   2
                    ///  / \
                    /// 1  4
                    ///   / \
                    ///  3  5
                    ///    / \
                    ///      6
                    /// ```
                    ///
                    /// The final insertion of element '6' should invoke a
                    /// left-rotation about element '2' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      4
                    ///    /   \
                    ///   2    5
                    ///  / \  / \
                    /// 1  3    6
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(2).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(4).is_ok());

                        assert!(instance.insert(3).is_ok());
                        assert!(instance.insert(5).is_ok());

                        assert!(instance.insert(6).is_ok());

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 4);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 2);
                        assert_eq!(left.balance, BalanceFactor::Balanced);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_some());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 1);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn left_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_right = unsafe { left.right.unwrap().as_ref() };

                        assert_eq!(left_right.element, 3);
                        assert_eq!(left_right.balance, BalanceFactor::Balanced);
                        assert_eq!(left_right.parent, Some(left_ptr));
                        assert!(left_right.left.is_none());
                        assert!(left_right.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 5);
                        assert_eq!(right.balance, BalanceFactor::Right);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_none());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 6);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }
            }

            mod does_left_right_rotation {
                use super::*;

                mod when_leaf_is_left_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///     5
                    ///    / \
                    ///   2  6
                    ///  / \
                    /// 1  4
                    ///   / \
                    ///  3
                    /// ```
                    ///
                    /// The final insertion of element '3' should invoke a
                    /// left-rotation about element '2' followed by a
                    /// right-rotation about element '5' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      4
                    ///    /   \
                    ///   2    5
                    ///  / \  / \
                    /// 1  3    6
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(5).is_ok());

                        assert!(instance.insert(2).is_ok());
                        assert!(instance.insert(6).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(4).is_ok());

                        assert!(instance.insert(3).is_ok());

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 4);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 2);
                        assert_eq!(left.balance, BalanceFactor::Balanced);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_some());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 1);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn left_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_right = unsafe { left.right.unwrap().as_ref() };

                        assert_eq!(left_right.element, 3);
                        assert_eq!(left_right.balance, BalanceFactor::Balanced);
                        assert_eq!(left_right.parent, Some(left_ptr));
                        assert!(left_right.left.is_none());
                        assert!(left_right.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 5);
                        assert_eq!(right.balance, BalanceFactor::Right);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_none());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 6);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }

                mod when_leaf_is_right_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///     5
                    ///    / \
                    ///   2  6
                    ///  / \
                    /// 1  3
                    ///   / \
                    ///     4
                    /// ```
                    ///
                    /// The final insertion of element '4' should invoke a
                    /// left-rotation about element '2' followed by a
                    /// right-rotation about element '5' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      3
                    ///    /   \
                    ///   2    5
                    ///  / \  / \
                    /// 1    4  6
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(5).is_ok());

                        assert!(instance.insert(2).is_ok());
                        assert!(instance.insert(6).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(3).is_ok());

                        assert!(instance.insert(4).is_ok());

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 3);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 2);
                        assert_eq!(left.balance, BalanceFactor::Left);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_none());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 1);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 5);
                        assert_eq!(right.balance, BalanceFactor::Balanced);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_some());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_left = unsafe { right.left.unwrap().as_ref() };

                        assert_eq!(right_left.element, 4);
                        assert_eq!(right_left.balance, BalanceFactor::Balanced);
                        assert_eq!(right_left.parent, Some(right_ptr));
                        assert!(right_left.left.is_none());
                        assert!(right_left.right.is_none());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 6);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }
            }

            mod does_right_rotation {
                use super::*;

                mod when_leaf_is_left_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///       5
                    ///      / \
                    ///     3  6
                    ///    / \
                    ///   2  4
                    ///  / \
                    /// 1
                    /// ```
                    ///
                    /// The final insertion of element '1' should invoke a
                    /// right-rotation about element '5' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      3
                    ///    /   \
                    ///   2    5
                    ///  / \  / \
                    /// 1    4  6
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(5).is_ok());

                        assert!(instance.insert(3).is_ok());
                        assert!(instance.insert(6).is_ok());

                        assert!(instance.insert(2).is_ok());
                        assert!(instance.insert(4).is_ok());

                        assert!(instance.insert(1).is_ok());

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 3);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 2);
                        assert_eq!(left.balance, BalanceFactor::Left);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_none());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 1);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 5);
                        assert_eq!(right.balance, BalanceFactor::Balanced);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_some());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_left = unsafe { right.left.unwrap().as_ref() };

                        assert_eq!(right_left.element, 4);
                        assert_eq!(right_left.balance, BalanceFactor::Balanced);
                        assert_eq!(right_left.parent, Some(right_ptr));
                        assert!(right_left.left.is_none());
                        assert!(right_left.right.is_none());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 6);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }

                mod when_leaf_is_right_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///       5
                    ///      / \
                    ///     3  6
                    ///    / \
                    ///   1  4
                    ///  / \
                    ///    2
                    /// ```
                    ///
                    /// The final insertion of element '2' should invoke a
                    /// right-rotation about element '5' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      3
                    ///    /   \
                    ///   1    5
                    ///  / \  / \
                    ///    2 4  6
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(5).is_ok());

                        assert!(instance.insert(3).is_ok());
                        assert!(instance.insert(6).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(4).is_ok());

                        assert!(instance.insert(2).is_ok());

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 3);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 1);
                        assert_eq!(left.balance, BalanceFactor::Right);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_none());
                        assert!(left.right.is_some());
                    }

                    #[test]
                    fn left_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_right = unsafe { left.right.unwrap().as_ref() };

                        assert_eq!(left_right.element, 2);
                        assert_eq!(left_right.balance, BalanceFactor::Balanced);
                        assert_eq!(left_right.parent, Some(left_ptr));
                        assert!(left_right.left.is_none());
                        assert!(left_right.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 5);
                        assert_eq!(right.balance, BalanceFactor::Balanced);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_some());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_left = unsafe { right.left.unwrap().as_ref() };

                        assert_eq!(right_left.element, 4);
                        assert_eq!(right_left.balance, BalanceFactor::Balanced);
                        assert_eq!(right_left.parent, Some(right_ptr));
                        assert!(right_left.left.is_none());
                        assert!(right_left.right.is_none());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 6);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }
            }

            mod does_right_left_rotation {
                use super::*;

                mod when_leaf_is_left_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///    2
                    ///   / \
                    ///  1  5
                    ///    / \
                    ///   4  6
                    ///  / \
                    /// 3
                    /// ```
                    ///
                    /// The final insertion of element '3' should invoke a
                    /// right-rotation about element '5' followed by a
                    /// left-rotation about element '2' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      4
                    ///    /   \
                    ///   2    5
                    ///  / \  / \
                    /// 1  3    6
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(2).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(5).is_ok());

                        assert!(instance.insert(4).is_ok());
                        assert!(instance.insert(6).is_ok());

                        assert!(instance.insert(3).is_ok());

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 4);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 2);
                        assert_eq!(left.balance, BalanceFactor::Balanced);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_some());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 1);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn left_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_right = unsafe { left.right.unwrap().as_ref() };

                        assert_eq!(left_right.element, 3);
                        assert_eq!(left_right.balance, BalanceFactor::Balanced);
                        assert_eq!(left_right.parent, Some(left_ptr));
                        assert!(left_right.left.is_none());
                        assert!(left_right.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 5);
                        assert_eq!(right.balance, BalanceFactor::Right);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_none());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 6);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }

                mod when_leaf_is_right_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///   2
                    ///  / \
                    /// 1  5
                    ///   / \
                    ///  3  6
                    /// / \
                    ///   4
                    /// ```
                    ///
                    /// The final insertion of element '4' should invoke a
                    /// right-rotation about element '5' followed by a
                    /// left-rotation about element '2' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      3
                    ///    /   \
                    ///   2    5
                    ///  / \  / \
                    /// 1    4  6
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(2).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(5).is_ok());

                        assert!(instance.insert(3).is_ok());
                        assert!(instance.insert(6).is_ok());

                        assert!(instance.insert(4).is_ok());

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 3);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 2);
                        assert_eq!(left.balance, BalanceFactor::Left);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_none());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 1);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 5);
                        assert_eq!(right.balance, BalanceFactor::Balanced);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_some());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_left = unsafe { right.left.unwrap().as_ref() };

                        assert_eq!(right_left.element, 4);
                        assert_eq!(right_left.balance, BalanceFactor::Balanced);
                        assert_eq!(right_left.parent, Some(right_ptr));
                        assert!(right_left.left.is_none());
                        assert!(right_left.right.is_none());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 6);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }
            }
        }

        mod remove {
            use super::*;

            #[test]
            fn when_empty() {
                let mut instance = AdelsonVelskyLandis::<usize>::default();

                assert_eq!(instance.remove(&0), None);
            }

            #[test]
            fn yields_element_when_contained() {
                let elements = 0..8;

                #[allow(clippy::from_iter_instead_of_collect)]
                let mut instance = AdelsonVelskyLandis::from_iter(elements.clone());

                for element in elements {
                    assert_eq!(instance.remove(&element), Some(element));
                }
            }

            #[test]
            fn yields_none_when_not_contained() {
                let mut instance = (0..8).collect::<AdelsonVelskyLandis<_>>();

                for element in 8..16 {
                    assert!(instance.remove(&element).is_none());
                }
            }

            mod does_no_rotation {
                use super::*;

                mod when_removing_root {
                    use super::*;

                    #[test]
                    fn when_only_root() {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(0).is_ok());

                        assert_eq!(instance.remove(&0), Some(0));

                        assert!(instance.root.is_none());
                    }

                    #[test]
                    fn when_only_left_child() {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(2).is_ok());
                        assert!(instance.insert(1).is_ok());

                        assert_eq!(instance.remove(&2), Some(2));

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 1);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_none());
                        assert!(root.right.is_none());
                    }

                    #[test]
                    fn when_only_right_child() {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(2).is_ok());

                        assert_eq!(instance.remove(&1), Some(1));

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 2);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_none());
                        assert!(root.right.is_none());
                    }

                    mod when_both_children {
                        use super::*;

                        mod when_no_right_grandchildren {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///   2
                            ///  / \
                            /// 1   3
                            /// ```
                            ///
                            /// The deletion of element '2' should invoke no
                            /// rotation thenceforth modifying the structure
                            /// to become:
                            ///
                            /// ```
                            ///   3
                            ///  / \
                            /// 1
                            /// ```
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(2).is_ok());

                                assert!(instance.insert(1).is_ok());
                                assert!(instance.insert(3).is_ok());

                                assert_eq!(instance.remove(&2), Some(2));

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 3);
                                assert_eq!(root.balance, BalanceFactor::Left);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_none());
                            }

                            #[test]
                            fn left() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 1);
                                assert_eq!(left.balance, BalanceFactor::Balanced);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_none());
                                assert!(left.right.is_none());
                            }
                        }

                        mod when_only_right_left_grandchild {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///   2
                            ///  / \
                            /// 1   4
                            ///    / \
                            ///   3
                            /// ```
                            ///
                            /// The deletion of element '2' should invoke no
                            /// rotation thenceforth modifying the structure
                            /// to become:
                            ///
                            /// ```
                            ///   3
                            ///  / \
                            /// 1  4
                            /// ```
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(2).is_ok());

                                assert!(instance.insert(1).is_ok());
                                assert!(instance.insert(4).is_ok());

                                assert!(instance.insert(3).is_ok());

                                assert_eq!(instance.remove(&2), Some(2));

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 3);
                                assert_eq!(root.balance, BalanceFactor::Balanced);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_some());
                            }

                            #[test]
                            fn left() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 1);
                                assert_eq!(left.balance, BalanceFactor::Balanced);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_none());
                                assert!(left.right.is_none());
                            }

                            #[test]
                            fn right() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { root.right.unwrap().as_ref() };

                                assert_eq!(right.element, 4);
                                assert_eq!(right.balance, BalanceFactor::Balanced);
                                assert_eq!(right.parent, Some(root_ptr));
                                assert!(right.left.is_none());
                                assert!(right.right.is_none());
                            }
                        }

                        mod when_only_right_right_grandchild {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///   2
                            ///  / \
                            /// 1   3
                            ///    / \
                            ///      4
                            /// ```
                            ///
                            /// The deletion of element '2' should invoke no
                            /// rotation thenceforth modifying the structure
                            /// to become:
                            ///
                            /// ```
                            ///   3
                            ///  / \
                            /// 1   4
                            /// ```
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(2).is_ok());

                                assert!(instance.insert(1).is_ok());
                                assert!(instance.insert(3).is_ok());

                                assert!(instance.insert(4).is_ok());

                                assert_eq!(instance.remove(&2), Some(2));

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 3);
                                assert_eq!(root.balance, BalanceFactor::Balanced);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_some());
                            }

                            #[test]
                            fn left() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 1);
                                assert_eq!(left.balance, BalanceFactor::Balanced);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_none());
                                assert!(left.right.is_none());
                            }

                            #[test]
                            fn right() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { root.right.unwrap().as_ref() };

                                assert_eq!(right.element, 4);
                                assert_eq!(right.balance, BalanceFactor::Balanced);
                                assert_eq!(right.parent, Some(root_ptr));
                                assert!(right.left.is_none());
                                assert!(right.right.is_none());
                            }
                        }

                        mod when_both_grandchildren {
                            use super::*;

                            mod when_no_great_grandchild {
                                use super::*;

                                /// Should create the following structure:
                                ///
                                /// ```
                                ///   2
                                ///  / \
                                /// 1   4
                                ///    / \
                                ///   3  5
                                /// ```
                                ///
                                /// The deletion of element '2' should invoke no
                                /// rotation thenceforth modifying the structure
                                /// to become:
                                ///
                                /// ```
                                ///   3
                                ///  / \
                                /// 1   4
                                ///    / \
                                ///      5
                                /// ```
                                fn setup() -> AdelsonVelskyLandis<usize> {
                                    let mut instance = AdelsonVelskyLandis::default();

                                    assert!(instance.insert(2).is_ok());

                                    assert!(instance.insert(1).is_ok());
                                    assert!(instance.insert(4).is_ok());

                                    assert!(instance.insert(3).is_ok());
                                    assert!(instance.insert(5).is_ok());

                                    assert_eq!(instance.remove(&2), Some(2));

                                    instance
                                }

                                #[test]
                                fn root() {
                                    let instance = setup();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let root = unsafe { instance.root.unwrap().as_ref() };

                                    assert_eq!(root.element, 3);
                                    assert_eq!(root.balance, BalanceFactor::Right);
                                    assert_eq!(root.parent, None);
                                    assert!(root.left.is_some());
                                    assert!(root.right.is_some());
                                }

                                #[test]
                                fn left() {
                                    let instance = setup();

                                    let root_ptr = instance.root.unwrap();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let root = unsafe { root_ptr.as_ref() };

                                    // SAFETY: no other reference exists to this node to alias.
                                    let left = unsafe { root.left.unwrap().as_ref() };

                                    assert_eq!(left.element, 1);
                                    assert_eq!(left.balance, BalanceFactor::Balanced);
                                    assert_eq!(left.parent, Some(root_ptr));
                                    assert!(left.left.is_none());
                                    assert!(left.right.is_none());
                                }

                                #[test]
                                fn right() {
                                    let instance = setup();

                                    let root_ptr = instance.root.unwrap();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let root = unsafe { root_ptr.as_ref() };

                                    // SAFETY: no other reference exists to this node to alias.
                                    let right = unsafe { root.right.unwrap().as_ref() };

                                    assert_eq!(right.element, 4);
                                    assert_eq!(right.balance, BalanceFactor::Right);
                                    assert_eq!(right.parent, Some(root_ptr));
                                    assert!(right.left.is_none());
                                    assert!(right.right.is_some());
                                }

                                #[test]
                                fn right_right() {
                                    let instance = setup();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let root = unsafe { instance.root.unwrap().as_ref() };

                                    let right_ptr = root.right.unwrap();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let right = unsafe { right_ptr.as_ref() };

                                    // SAFETY: no other reference exists to this node to alias.
                                    let right_right = unsafe { right.right.unwrap().as_ref() };

                                    assert_eq!(right_right.element, 5);
                                    assert_eq!(right_right.balance, BalanceFactor::Balanced);
                                    assert_eq!(right_right.parent, Some(right_ptr));
                                    assert!(right_right.left.is_none());
                                    assert!(right_right.right.is_none());
                                }
                            }

                            mod when_great_grandchild {
                                use super::*;

                                /// Should create the following structure:
                                ///
                                /// ```
                                ///      4
                                ///    /   \
                                ///   2     7
                                ///  / \   / \
                                /// 1  3  5  8
                                ///      / \
                                ///        6
                                /// ```
                                ///
                                /// The deletion of element '4' should invoke no
                                /// rotation thenceforth modifying the structure
                                /// to become:
                                ///
                                /// ```
                                ///      5
                                ///    /   \
                                ///   2     7
                                ///  / \   / \
                                /// 1  3  6  8
                                /// ```
                                fn setup() -> AdelsonVelskyLandis<usize> {
                                    let mut instance = AdelsonVelskyLandis::default();

                                    assert!(instance.insert(4).is_ok());

                                    assert!(instance.insert(2).is_ok());
                                    assert!(instance.insert(7).is_ok());

                                    assert!(instance.insert(1).is_ok());
                                    assert!(instance.insert(3).is_ok());

                                    assert!(instance.insert(5).is_ok());
                                    assert!(instance.insert(8).is_ok());

                                    assert!(instance.insert(6).is_ok());

                                    assert_eq!(instance.remove(&4), Some(4));

                                    instance
                                }

                                #[test]
                                fn root() {
                                    let instance = setup();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let root = unsafe { instance.root.unwrap().as_ref() };

                                    assert_eq!(root.element, 5);
                                    assert_eq!(root.balance, BalanceFactor::Balanced);
                                    assert_eq!(root.parent, None);
                                    assert!(root.left.is_some());
                                    assert!(root.right.is_some());
                                }

                                #[test]
                                fn left() {
                                    let instance = setup();

                                    let root_ptr = instance.root.unwrap();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let root = unsafe { root_ptr.as_ref() };

                                    // SAFETY: no other reference exists to this node to alias.
                                    let left = unsafe { root.left.unwrap().as_ref() };

                                    assert_eq!(left.element, 2);
                                    assert_eq!(left.balance, BalanceFactor::Balanced);
                                    assert_eq!(left.parent, Some(root_ptr));
                                    assert!(left.left.is_some());
                                    assert!(left.right.is_some());
                                }

                                #[test]
                                fn left_left() {
                                    let instance = setup();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let root = unsafe { instance.root.unwrap().as_ref() };

                                    let left_ptr = root.left.unwrap();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let left = unsafe { left_ptr.as_ref() };

                                    // SAFETY: no other reference exists to this node to alias.
                                    let left_left = unsafe { left.left.unwrap().as_ref() };

                                    assert_eq!(left_left.element, 1);
                                    assert_eq!(left_left.balance, BalanceFactor::Balanced);
                                    assert_eq!(left_left.parent, Some(left_ptr));
                                    assert!(left_left.left.is_none());
                                    assert!(left_left.right.is_none());
                                }

                                #[test]
                                fn left_right() {
                                    let instance = setup();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let root = unsafe { instance.root.unwrap().as_ref() };

                                    let left_ptr = root.left.unwrap();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let left = unsafe { left_ptr.as_ref() };

                                    // SAFETY: no other reference exists to this node to alias.
                                    let left_right = unsafe { left.right.unwrap().as_ref() };

                                    assert_eq!(left_right.element, 3);
                                    assert_eq!(left_right.balance, BalanceFactor::Balanced);
                                    assert_eq!(left_right.parent, Some(left_ptr));
                                    assert!(left_right.left.is_none());
                                    assert!(left_right.right.is_none());
                                }

                                #[test]
                                fn right() {
                                    let instance = setup();

                                    let root_ptr = instance.root.unwrap();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let root = unsafe { root_ptr.as_ref() };

                                    // SAFETY: no other reference exists to this node to alias.
                                    let right = unsafe { root.right.unwrap().as_ref() };

                                    assert_eq!(right.element, 7);
                                    assert_eq!(right.balance, BalanceFactor::Balanced);
                                    assert_eq!(right.parent, Some(root_ptr));
                                    assert!(right.left.is_some());
                                    assert!(right.right.is_some());
                                }

                                #[test]
                                fn right_left() {
                                    let instance = setup();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let root = unsafe { instance.root.unwrap().as_ref() };

                                    let right_ptr = root.right.unwrap();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let right = unsafe { right_ptr.as_ref() };

                                    // SAFETY: no other reference exists to this node to alias.
                                    let right_left = unsafe { right.left.unwrap().as_ref() };

                                    assert_eq!(right_left.element, 6);
                                    assert_eq!(right_left.balance, BalanceFactor::Balanced);
                                    assert_eq!(right_left.parent, Some(right_ptr));
                                    assert!(right_left.left.is_none());
                                    assert!(right_left.right.is_none());
                                }

                                #[test]
                                fn right_right() {
                                    let instance = setup();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let root = unsafe { instance.root.unwrap().as_ref() };

                                    let right_ptr = root.right.unwrap();

                                    // SAFETY: no other reference exists to this node to alias.
                                    let right = unsafe { right_ptr.as_ref() };

                                    // SAFETY: no other reference exists to this node to alias.
                                    let right_right = unsafe { right.right.unwrap().as_ref() };

                                    assert_eq!(right_right.element, 8);
                                    assert_eq!(right_right.balance, BalanceFactor::Balanced);
                                    assert_eq!(right_right.parent, Some(right_ptr));
                                    assert!(right_right.left.is_none());
                                    assert!(right_right.right.is_none());
                                }
                            }
                        }
                    }
                }

                mod when_creates_single_imbalance {
                    use super::*;

                    mod when_left_imbalance {
                        use super::*;

                        /// Should create the following structure:
                        ///
                        /// ```
                        ///   2
                        ///  / \
                        /// 1  3
                        /// ```
                        ///
                        /// The deletion of element '3' should invoke no
                        /// rotation thenceforth modifying the structure
                        /// to become:
                        ///
                        /// ```
                        ///   2
                        ///  / \
                        /// 1
                        /// ```
                        fn setup() -> AdelsonVelskyLandis<usize> {
                            let mut instance = AdelsonVelskyLandis::default();

                            assert!(instance.insert(2).is_ok());

                            assert!(instance.insert(1).is_ok());
                            assert!(instance.insert(3).is_ok());

                            assert_eq!(instance.remove(&3), Some(3));

                            instance
                        }

                        #[test]
                        fn root() {
                            let instance = setup();

                            // SAFETY: no other reference exists to this node to alias.
                            let root = unsafe { instance.root.unwrap().as_ref() };

                            assert_eq!(root.element, 2);
                            assert_eq!(root.balance, BalanceFactor::Left);
                            assert_eq!(root.parent, None);
                            assert!(root.left.is_some());
                            assert!(root.right.is_none());
                        }

                        #[test]
                        fn left_child() {
                            let instance = setup();

                            let root_ptr = instance.root.unwrap();

                            // SAFETY: no other reference exists to this node to alias.
                            let root = unsafe { root_ptr.as_ref() };

                            // SAFETY: no other reference exists to this node to alias.
                            let left = unsafe { root.left.unwrap().as_ref() };

                            assert_eq!(left.element, 1);
                            assert_eq!(left.balance, BalanceFactor::Balanced);
                            assert_eq!(left.parent, Some(root_ptr));
                            assert!(left.left.is_none());
                            assert!(left.right.is_none());
                        }
                    }

                    mod when_right_imbalance {
                        use super::*;

                        /// Should create the following structure:
                        ///
                        /// ```
                        ///   2
                        ///  / \
                        /// 1  3
                        /// ```
                        ///
                        /// The deletion of element '1' should invoke no
                        /// rotation thenceforth modifying the structure
                        /// to become:
                        ///
                        /// ```
                        ///  2
                        /// / \
                        ///   3
                        /// ```
                        fn setup() -> AdelsonVelskyLandis<usize> {
                            let mut instance = AdelsonVelskyLandis::default();

                            assert!(instance.insert(2).is_ok());

                            assert!(instance.insert(1).is_ok());
                            assert!(instance.insert(3).is_ok());

                            assert_eq!(instance.remove(&1), Some(1));

                            instance
                        }

                        #[test]
                        fn root() {
                            let instance = setup();

                            // SAFETY: no other reference exists to this node to alias.
                            let root = unsafe { instance.root.unwrap().as_ref() };

                            assert_eq!(root.element, 2);
                            assert_eq!(root.balance, BalanceFactor::Right);
                            assert_eq!(root.parent, None);
                            assert!(root.left.is_none());
                            assert!(root.right.is_some());
                        }

                        #[test]
                        fn right_child() {
                            let instance = setup();

                            let root_ptr = instance.root.unwrap();

                            // SAFETY: no other reference exists to this node to alias.
                            let root = unsafe { root_ptr.as_ref() };

                            // SAFETY: no other reference exists to this node to alias.
                            let right = unsafe { root.right.unwrap().as_ref() };

                            assert_eq!(right.element, 3);
                            assert_eq!(right.balance, BalanceFactor::Balanced);
                            assert_eq!(right.parent, Some(root_ptr));
                            assert!(right.left.is_none());
                            assert!(right.right.is_none());
                        }
                    }
                }

                mod when_balancing_unbalanced_tree {
                    use super::*;

                    mod when_left_imbalance {
                        use super::*;

                        mod when_leaf_is_left_child {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///     3
                            ///    / \
                            ///   2   4
                            ///  / \
                            /// 1
                            /// ```
                            ///
                            /// The deletion of element '1' should invoke no
                            /// rotation thenceforth modifying the structure
                            /// to become:
                            ///
                            /// ```
                            ///   3
                            ///  / \
                            /// 2  4
                            /// ```
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(3).is_ok());

                                assert!(instance.insert(2).is_ok());
                                assert!(instance.insert(4).is_ok());

                                assert!(instance.insert(1).is_ok());

                                assert_eq!(instance.remove(&1), Some(1));

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 3);
                                assert_eq!(root.balance, BalanceFactor::Balanced);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_some());
                            }

                            #[test]
                            fn left_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 2);
                                assert_eq!(left.balance, BalanceFactor::Balanced);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_none());
                                assert!(left.right.is_none());
                            }

                            #[test]
                            fn right_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { root.right.unwrap().as_ref() };

                                assert_eq!(right.element, 4);
                                assert_eq!(right.balance, BalanceFactor::Balanced);
                                assert_eq!(right.parent, Some(root_ptr));
                                assert!(right.left.is_none());
                                assert!(right.right.is_none());
                            }
                        }

                        mod when_leaf_is_right_child {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///    3
                            ///   / \
                            ///  1   4
                            /// / \
                            ///   2
                            /// ```
                            ///
                            /// The deletion of element '2' should invoke no
                            /// rotation thenceforth modifying the structure
                            /// to become:
                            ///
                            /// ```
                            ///   3
                            ///  / \
                            /// 1  4
                            /// ```
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(3).is_ok());

                                assert!(instance.insert(1).is_ok());
                                assert!(instance.insert(4).is_ok());

                                assert!(instance.insert(2).is_ok());

                                assert_eq!(instance.remove(&2), Some(2));

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 3);
                                assert_eq!(root.balance, BalanceFactor::Balanced);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_some());
                            }

                            #[test]
                            fn left_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 1);
                                assert_eq!(left.balance, BalanceFactor::Balanced);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_none());
                                assert!(left.right.is_none());
                            }

                            #[test]
                            fn right_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { root.right.unwrap().as_ref() };

                                assert_eq!(right.element, 4);
                                assert_eq!(right.balance, BalanceFactor::Balanced);
                                assert_eq!(right.parent, Some(root_ptr));
                                assert!(right.left.is_none());
                                assert!(right.right.is_none());
                            }
                        }
                    }

                    mod when_right_imbalance {
                        use super::*;

                        mod when_leaf_is_left_child {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///   2
                            ///  / \
                            /// 1   4
                            ///    / \
                            ///   3
                            /// ```
                            ///
                            /// The deletion of element '3' should invoke no
                            /// rotation thenceforth modifying the structure
                            /// to become:
                            ///
                            /// ```
                            ///   2
                            ///  / \
                            /// 1  4
                            /// ```
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(2).is_ok());

                                assert!(instance.insert(1).is_ok());
                                assert!(instance.insert(4).is_ok());

                                assert!(instance.insert(3).is_ok());

                                assert_eq!(instance.remove(&3), Some(3));

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 2);
                                assert_eq!(root.balance, BalanceFactor::Balanced);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_some());
                            }

                            #[test]
                            fn left_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 1);
                                assert_eq!(left.balance, BalanceFactor::Balanced);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_none());
                                assert!(left.right.is_none());
                            }

                            #[test]
                            fn right_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { root.right.unwrap().as_ref() };

                                assert_eq!(right.element, 4);
                                assert_eq!(right.balance, BalanceFactor::Balanced);
                                assert_eq!(right.parent, Some(root_ptr));
                                assert!(right.left.is_none());
                                assert!(right.right.is_none());
                            }
                        }

                        mod when_leaf_is_right_child {
                            use super::*;

                            /// Should create the following structure:
                            ///
                            /// ```
                            ///   2
                            ///  / \
                            /// 1   3
                            ///    / \
                            ///      4
                            /// ```
                            ///
                            /// The deletion of element '4' should invoke no
                            /// rotation thenceforth modifying the structure
                            /// to become:
                            ///
                            /// ```
                            ///   2
                            ///  / \
                            /// 1  3
                            /// ```
                            fn setup() -> AdelsonVelskyLandis<usize> {
                                let mut instance = AdelsonVelskyLandis::default();

                                assert!(instance.insert(2).is_ok());

                                assert!(instance.insert(1).is_ok());
                                assert!(instance.insert(3).is_ok());

                                assert!(instance.insert(4).is_ok());

                                assert_eq!(instance.remove(&4), Some(4));

                                instance
                            }

                            #[test]
                            fn root() {
                                let instance = setup();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { instance.root.unwrap().as_ref() };

                                assert_eq!(root.element, 2);
                                assert_eq!(root.balance, BalanceFactor::Balanced);
                                assert_eq!(root.parent, None);
                                assert!(root.left.is_some());
                                assert!(root.right.is_some());
                            }

                            #[test]
                            fn left_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let left = unsafe { root.left.unwrap().as_ref() };

                                assert_eq!(left.element, 1);
                                assert_eq!(left.balance, BalanceFactor::Balanced);
                                assert_eq!(left.parent, Some(root_ptr));
                                assert!(left.left.is_none());
                                assert!(left.right.is_none());
                            }

                            #[test]
                            fn right_child() {
                                let instance = setup();

                                let root_ptr = instance.root.unwrap();

                                // SAFETY: no other reference exists to this node to alias.
                                let root = unsafe { root_ptr.as_ref() };

                                // SAFETY: no other reference exists to this node to alias.
                                let right = unsafe { root.right.unwrap().as_ref() };

                                assert_eq!(right.element, 3);
                                assert_eq!(right.balance, BalanceFactor::Balanced);
                                assert_eq!(right.parent, Some(root_ptr));
                                assert!(right.left.is_none());
                                assert!(right.right.is_none());
                            }
                        }
                    }
                }
            }

            mod does_left_rotation {
                use super::*;

                mod when_leaf_is_left_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///      3
                    ///    /   \
                    ///   2     5
                    ///  / \   / \
                    /// 1     4  7
                    ///         / \
                    ///        6  8
                    /// ```
                    ///
                    /// The deletion of element '1' should invoke a
                    /// left-rotation about element '3' thenceforth
                    /// modifying the structure to become:
                    ///
                    /// ```
                    ///      5
                    ///    /   \
                    ///   3    7
                    ///  / \  / \
                    /// 2  4 6  8
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(3).is_ok());

                        assert!(instance.insert(2).is_ok());
                        assert!(instance.insert(5).is_ok());

                        assert!(instance.insert(1).is_ok());

                        assert!(instance.insert(4).is_ok());
                        assert!(instance.insert(7).is_ok());

                        assert!(instance.insert(6).is_ok());
                        assert!(instance.insert(8).is_ok());

                        assert_eq!(instance.remove(&1), Some(1));

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 5);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 3);
                        assert_eq!(left.balance, BalanceFactor::Balanced);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_some());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 2);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn left_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_right = unsafe { left.right.unwrap().as_ref() };

                        assert_eq!(left_right.element, 4);
                        assert_eq!(left_right.balance, BalanceFactor::Balanced);
                        assert_eq!(left_right.parent, Some(left_ptr));
                        assert!(left_right.left.is_none());
                        assert!(left_right.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 7);
                        assert_eq!(right.balance, BalanceFactor::Balanced);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_some());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_left = unsafe { right.left.unwrap().as_ref() };

                        assert_eq!(right_left.element, 6);
                        assert_eq!(right_left.balance, BalanceFactor::Balanced);
                        assert_eq!(right_left.parent, Some(right_ptr));
                        assert!(right_left.left.is_none());
                        assert!(right_left.right.is_none());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 8);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }

                mod when_leaf_is_right_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///     3
                    ///   /   \
                    ///  1     5
                    /// / \   / \
                    ///   2  4  7
                    ///        / \
                    ///       6  8
                    /// ```
                    ///
                    /// The deletion of element '2' should invoke a
                    /// left-rotation about element '3' thenceforth
                    /// modifying the structure to become:
                    ///
                    /// ```
                    ///      5
                    ///    /   \
                    ///   3    7
                    ///  / \  / \
                    /// 1  4 6  8
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(3).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(5).is_ok());

                        assert!(instance.insert(2).is_ok());

                        assert!(instance.insert(4).is_ok());
                        assert!(instance.insert(7).is_ok());

                        assert!(instance.insert(6).is_ok());
                        assert!(instance.insert(8).is_ok());

                        assert_eq!(instance.remove(&2), Some(2));

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 5);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 3);
                        assert_eq!(left.balance, BalanceFactor::Balanced);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_some());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 1);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn left_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_right = unsafe { left.right.unwrap().as_ref() };

                        assert_eq!(left_right.element, 4);
                        assert_eq!(left_right.balance, BalanceFactor::Balanced);
                        assert_eq!(left_right.parent, Some(left_ptr));
                        assert!(left_right.left.is_none());
                        assert!(left_right.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 7);
                        assert_eq!(right.balance, BalanceFactor::Balanced);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_some());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_left = unsafe { right.left.unwrap().as_ref() };

                        assert_eq!(right_left.element, 6);
                        assert_eq!(right_left.balance, BalanceFactor::Balanced);
                        assert_eq!(right_left.parent, Some(right_ptr));
                        assert!(right_left.left.is_none());
                        assert!(right_left.right.is_none());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 8);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }
            }

            mod does_left_right_rotation {
                use super::*;

                mod when_leaf_is_left_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///       6
                    ///    /     \
                    ///   2      8
                    ///  / \    / \
                    /// 1  4   7
                    ///   / \
                    ///  3  5
                    /// ```
                    ///
                    /// The deletion of element '7' should invoke a
                    /// left-rotation about element '2' followed by a
                    /// right-rotation about element '6' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      4
                    ///    /   \
                    ///   2    6
                    ///  / \  / \
                    /// 1  3 5  8
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(6).is_ok());

                        assert!(instance.insert(2).is_ok());
                        assert!(instance.insert(8).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(4).is_ok());

                        assert!(instance.insert(7).is_ok());

                        assert!(instance.insert(3).is_ok());
                        assert!(instance.insert(5).is_ok());

                        assert_eq!(instance.remove(&7), Some(7));

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 4);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 2);
                        assert_eq!(left.balance, BalanceFactor::Balanced);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_some());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 1);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn left_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_right = unsafe { left.right.unwrap().as_ref() };

                        assert_eq!(left_right.element, 3);
                        assert_eq!(left_right.balance, BalanceFactor::Balanced);
                        assert_eq!(left_right.parent, Some(left_ptr));
                        assert!(left_right.left.is_none());
                        assert!(left_right.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 6);
                        assert_eq!(right.balance, BalanceFactor::Balanced);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_some());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_left = unsafe { right.left.unwrap().as_ref() };

                        assert_eq!(right_left.element, 5);
                        assert_eq!(right_left.balance, BalanceFactor::Balanced);
                        assert_eq!(right_left.parent, Some(right_ptr));
                        assert!(right_left.left.is_none());
                        assert!(right_left.right.is_none());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 8);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }

                mod when_leaf_is_right_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///      6
                    ///    /   \
                    ///   2    7
                    ///  / \  / \
                    /// 1  4    8
                    ///   / \
                    ///  3  5
                    /// ```
                    ///
                    /// The deletion of element '8' should invoke a
                    /// left-rotation about element '2' followed by a
                    /// right-rotation about element '6' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      4
                    ///    /   \
                    ///   2    6
                    ///  / \  / \
                    /// 1  3 5  7
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(6).is_ok());

                        assert!(instance.insert(2).is_ok());
                        assert!(instance.insert(7).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(4).is_ok());

                        assert!(instance.insert(8).is_ok());

                        assert!(instance.insert(3).is_ok());
                        assert!(instance.insert(5).is_ok());

                        assert_eq!(instance.remove(&8), Some(8));

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 4);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 2);
                        assert_eq!(left.balance, BalanceFactor::Balanced);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_some());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 1);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn left_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_right = unsafe { left.right.unwrap().as_ref() };

                        assert_eq!(left_right.element, 3);
                        assert_eq!(left_right.balance, BalanceFactor::Balanced);
                        assert_eq!(left_right.parent, Some(left_ptr));
                        assert!(left_right.left.is_none());
                        assert!(left_right.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 6);
                        assert_eq!(right.balance, BalanceFactor::Balanced);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_some());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_left = unsafe { right.left.unwrap().as_ref() };

                        assert_eq!(right_left.element, 5);
                        assert_eq!(right_left.balance, BalanceFactor::Balanced);
                        assert_eq!(right_left.parent, Some(right_ptr));
                        assert!(right_left.left.is_none());
                        assert!(right_left.right.is_none());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 7);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }
            }

            mod does_right_rotation {
                use super::*;

                mod when_leaf_is_left_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///        6
                    ///      /   \
                    ///     4    8
                    ///    / \  / \
                    ///   2  5 7
                    ///  / \
                    /// 1  3
                    /// ```
                    ///
                    /// The deletion of element '7' should invoke a
                    /// right-rotation about element '6' thenceforth
                    /// modifying the structure to become:
                    ///
                    /// ```
                    ///      4
                    ///    /   \
                    ///   2    6
                    ///  / \  / \
                    /// 1  3 5  8
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(6).is_ok());

                        assert!(instance.insert(4).is_ok());
                        assert!(instance.insert(8).is_ok());

                        assert!(instance.insert(2).is_ok());
                        assert!(instance.insert(5).is_ok());

                        assert!(instance.insert(7).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(3).is_ok());

                        assert_eq!(instance.remove(&7), Some(7));

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 4);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 2);
                        assert_eq!(left.balance, BalanceFactor::Balanced);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_some());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 1);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn left_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_right = unsafe { left.right.unwrap().as_ref() };

                        assert_eq!(left_right.element, 3);
                        assert_eq!(left_right.balance, BalanceFactor::Balanced);
                        assert_eq!(left_right.parent, Some(left_ptr));
                        assert!(left_right.left.is_none());
                        assert!(left_right.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 6);
                        assert_eq!(right.balance, BalanceFactor::Balanced);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_some());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_left = unsafe { right.left.unwrap().as_ref() };

                        assert_eq!(right_left.element, 5);
                        assert_eq!(right_left.balance, BalanceFactor::Balanced);
                        assert_eq!(right_left.parent, Some(right_ptr));
                        assert!(right_left.left.is_none());
                        assert!(right_left.right.is_none());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 8);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }

                mod when_leaf_is_right_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///        6
                    ///      /   \
                    ///     4    7
                    ///    / \  / \
                    ///   2  5    8
                    ///  / \
                    /// 1  3
                    /// ```
                    ///
                    /// The deletion of element '8' should invoke a
                    /// right-rotation about element '6' thenceforth
                    /// modifying the structure to become:
                    ///
                    /// ```
                    ///      4
                    ///    /   \
                    ///   2    6
                    ///  / \  / \
                    /// 1  3 5  7
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(6).is_ok());

                        assert!(instance.insert(4).is_ok());
                        assert!(instance.insert(7).is_ok());

                        assert!(instance.insert(2).is_ok());
                        assert!(instance.insert(5).is_ok());

                        assert!(instance.insert(8).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(3).is_ok());

                        assert_eq!(instance.remove(&8), Some(8));

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 4);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 2);
                        assert_eq!(left.balance, BalanceFactor::Balanced);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_some());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 1);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn left_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_right = unsafe { left.right.unwrap().as_ref() };

                        assert_eq!(left_right.element, 3);
                        assert_eq!(left_right.balance, BalanceFactor::Balanced);
                        assert_eq!(left_right.parent, Some(left_ptr));
                        assert!(left_right.left.is_none());
                        assert!(left_right.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 6);
                        assert_eq!(right.balance, BalanceFactor::Balanced);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_some());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_left = unsafe { right.left.unwrap().as_ref() };

                        assert_eq!(right_left.element, 5);
                        assert_eq!(right_left.balance, BalanceFactor::Balanced);
                        assert_eq!(right_left.parent, Some(right_ptr));
                        assert!(right_left.left.is_none());
                        assert!(right_left.right.is_none());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 7);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }
            }

            mod does_right_left_rotation {
                use super::*;

                mod when_leaf_is_left_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///       3
                    ///    /    \
                    ///   2     7
                    ///  / \   / \
                    /// 1     5  8
                    ///      / \
                    ///     4  6
                    /// ```
                    ///
                    /// The deletion of element '1' should invoke a
                    /// right-rotation about element '7' followed by a
                    /// left-rotation about element '3' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      5
                    ///    /   \
                    ///   3    7
                    ///  / \  / \
                    /// 2  4 6  8
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(3).is_ok());

                        assert!(instance.insert(2).is_ok());
                        assert!(instance.insert(7).is_ok());

                        assert!(instance.insert(1).is_ok());

                        assert!(instance.insert(5).is_ok());
                        assert!(instance.insert(8).is_ok());

                        assert!(instance.insert(4).is_ok());
                        assert!(instance.insert(6).is_ok());

                        assert_eq!(instance.remove(&1), Some(1));

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 5);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 3);
                        assert_eq!(left.balance, BalanceFactor::Balanced);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_some());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 2);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn left_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_right = unsafe { left.right.unwrap().as_ref() };

                        assert_eq!(left_right.element, 4);
                        assert_eq!(left_right.balance, BalanceFactor::Balanced);
                        assert_eq!(left_right.parent, Some(left_ptr));
                        assert!(left_right.left.is_none());
                        assert!(left_right.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 7);
                        assert_eq!(right.balance, BalanceFactor::Balanced);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_some());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_left = unsafe { right.left.unwrap().as_ref() };

                        assert_eq!(right_left.element, 6);
                        assert_eq!(right_left.balance, BalanceFactor::Balanced);
                        assert_eq!(right_left.parent, Some(right_ptr));
                        assert!(right_left.left.is_none());
                        assert!(right_left.right.is_none());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 8);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }

                mod when_leaf_is_right_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///      3
                    ///   /    \
                    ///  1     7
                    /// / \   / \
                    ///   2  5  8
                    ///     / \
                    ///    4  6
                    /// ```
                    ///
                    /// The deletion of element '2' should invoke a
                    /// right-rotation about element '7' followed by a
                    /// left-rotation about element '3' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      5
                    ///    /   \
                    ///   3    7
                    ///  / \  / \
                    /// 1  4 6  8
                    /// ```
                    fn setup() -> AdelsonVelskyLandis<usize> {
                        let mut instance = AdelsonVelskyLandis::default();

                        assert!(instance.insert(3).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(7).is_ok());

                        assert!(instance.insert(2).is_ok());

                        assert!(instance.insert(5).is_ok());
                        assert!(instance.insert(8).is_ok());

                        assert!(instance.insert(4).is_ok());
                        assert!(instance.insert(6).is_ok());

                        assert_eq!(instance.remove(&2), Some(2));

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 5);
                        assert_eq!(root.balance, BalanceFactor::Balanced);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn left_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, 3);
                        assert_eq!(left.balance, BalanceFactor::Balanced);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert!(left.left.is_some());
                        assert!(left.right.is_some());
                    }

                    #[test]
                    fn left_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_left = unsafe { left.left.unwrap().as_ref() };

                        assert_eq!(left_left.element, 1);
                        assert_eq!(left_left.balance, BalanceFactor::Balanced);
                        assert_eq!(left_left.parent, Some(left_ptr));
                        assert!(left_left.left.is_none());
                        assert!(left_left.right.is_none());
                    }

                    #[test]
                    fn left_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let left_ptr = root.left.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { left_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left_right = unsafe { left.right.unwrap().as_ref() };

                        assert_eq!(left_right.element, 4);
                        assert_eq!(left_right.balance, BalanceFactor::Balanced);
                        assert_eq!(left_right.parent, Some(left_ptr));
                        assert!(left_right.left.is_none());
                        assert!(left_right.right.is_none());
                    }

                    #[test]
                    fn right_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 7);
                        assert_eq!(right.balance, BalanceFactor::Balanced);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert!(right.left.is_some());
                        assert!(right.right.is_some());
                    }

                    #[test]
                    fn right_left_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_left = unsafe { right.left.unwrap().as_ref() };

                        assert_eq!(right_left.element, 6);
                        assert_eq!(right_left.balance, BalanceFactor::Balanced);
                        assert_eq!(right_left.parent, Some(right_ptr));
                        assert!(right_left.left.is_none());
                        assert!(right_left.right.is_none());
                    }

                    #[test]
                    fn right_right_grandchild() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        let right_ptr = root.right.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { right_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right_right = unsafe { right.right.unwrap().as_ref() };

                        assert_eq!(right_right.element, 8);
                        assert_eq!(right_right.balance, BalanceFactor::Balanced);
                        assert_eq!(right_right.parent, Some(right_ptr));
                        assert!(right_right.left.is_none());
                        assert!(right_right.right.is_none());
                    }
                }
            }
        }
    }

    mod default {
        use super::*;

        #[test]
        fn is_empty() {
            let instance = AdelsonVelskyLandis::<usize>::default();

            assert!(instance.root.is_none());
        }
    }

    mod iterator {
        use super::*;

        mod from {
            use super::*;

            #[test]
            fn when_empty() {
                #[expect(clippy::from_iter_instead_of_collect)]
                let instance = AdelsonVelskyLandis::<usize>::from_iter(core::iter::empty());

                assert!(instance.root.is_none());
            }

            mod ignores_duplicate_elements {
                use super::*;

                #[test]
                fn does_not_modify_existing_element() {
                    todo!()
                }

                #[test]
                fn drops_duplicates() {
                    todo!()
                }
            }
        }
    }
}
