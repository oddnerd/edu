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
pub struct AdelsonVelsoLandis<T> {
    /// The [`Node`] that is defined as the root.
    root: Option<core::ptr::NonNull<Node<T>>>,
}

impl<T: Ord> AdelsonVelsoLandis<T> {
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
    /// todo!("yields ok element");
    /// todo!("yields err element");
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
    /// todo!("yields some element if found");
    /// todo!("yields none if not found");
    /// ```
    pub fn remove(&mut self, element: &T) -> Option<T> {
        todo!("remove the element")
    }
}

impl<T> Default for AdelsonVelsoLandis<T> {
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

impl<T: Ord> FromIterator<T> for AdelsonVelsoLandis<T> {
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
        let mut instance = AdelsonVelsoLandis::default();

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
    /// TODO
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
            (None, None | Some(_)) => unreachable!("old root should become the left child"),
        };

        root_node.balance = match (root_node.left, root_node.right) {
            (Some(_), Some(_)) | (None, None) => BalanceFactor::Balanced,
            (Some(_), None) => BalanceFactor::Left,
            (None, Some(_)) => unreachable!("logic error to rotate when not imbalanced"),
        };

        right_ptr
    }

    /// TODO
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
            (None | Some(_), None) => unreachable!("old root should become the right child"),
        };

        root_node.balance = match (root_node.left, root_node.right) {
            (Some(_), Some(_)) | (None, None) => BalanceFactor::Balanced,
            (None, Some(_)) => BalanceFactor::Right,
            (Some(_), None) => unreachable!("logic error to rotate when not imbalanced"),
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
                let mut instance = AdelsonVelsoLandis::<i32>::default();

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
                let mut instance = AdelsonVelsoLandis::default();

                for element in 0..=5 {
                    assert_eq!(instance.insert(element), Ok(&element));
                }
            }

            #[test]
            fn yields_error_when_already_contained() {
                let elements = 0..8;

                #[allow(clippy::from_iter_instead_of_collect)]
                let mut instance = AdelsonVelsoLandis::from_iter(elements.clone());

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
                        fn setup() -> AdelsonVelsoLandis<usize> {
                            let mut instance = AdelsonVelsoLandis::default();

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
                        fn setup() -> AdelsonVelsoLandis<usize> {
                            let mut instance = AdelsonVelsoLandis::default();

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
                            fn setup() -> AdelsonVelsoLandis<usize> {
                                let mut instance = AdelsonVelsoLandis::default();

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
                            fn setup() -> AdelsonVelsoLandis<usize> {
                                let mut instance = AdelsonVelsoLandis::default();

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
                            fn setup() -> AdelsonVelsoLandis<usize> {
                                let mut instance = AdelsonVelsoLandis::default();

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
                            fn setup() -> AdelsonVelsoLandis<usize> {
                                let mut instance = AdelsonVelsoLandis::default();

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
                            fn setup() -> AdelsonVelsoLandis<usize> {
                                let mut instance = AdelsonVelsoLandis::default();

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
                            fn setup() -> AdelsonVelsoLandis<usize> {
                                let mut instance = AdelsonVelsoLandis::default();

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
                            fn setup() -> AdelsonVelsoLandis<usize> {
                                let mut instance = AdelsonVelsoLandis::default();

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
                            fn setup() -> AdelsonVelsoLandis<usize> {
                                let mut instance = AdelsonVelsoLandis::default();

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
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        let mut instance = AdelsonVelsoLandis::default();

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
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        let mut instance = AdelsonVelsoLandis::default();

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
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        let mut instance = AdelsonVelsoLandis::default();

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
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        let mut instance = AdelsonVelsoLandis::default();

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
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        let mut instance = AdelsonVelsoLandis::default();

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
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        let mut instance = AdelsonVelsoLandis::default();

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
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        let mut instance = AdelsonVelsoLandis::default();

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
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        let mut instance = AdelsonVelsoLandis::default();

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
                let mut instance = AdelsonVelsoLandis::<usize>::default();

                assert_eq!(instance.remove(&0), None);
            }

            #[test]
            fn yields_element_when_contained() {
                let elements = 0..8;

                #[allow(clippy::from_iter_instead_of_collect)]
                let mut instance = AdelsonVelsoLandis::from_iter(elements.clone());

                for element in elements {
                    assert_eq!(instance.remove(&element), Some(element));
                }
            }

            #[test]
            fn yields_none_when_not_contained() {
                let mut instance = (0..8).collect::<AdelsonVelsoLandis<_>>();

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
                        let mut instance = AdelsonVelsoLandis::default();

                        assert!(instance.insert(0).is_ok());

                        assert_eq!(instance.remove(&0), Some(0));

                        assert!(instance.root.is_none());
                    }

                    #[test]
                    fn when_only_left_child() {
                        let mut instance = AdelsonVelsoLandis::default();

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
                        let mut instance = AdelsonVelsoLandis::default();

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
                        /// The removal of element '2' should swap elements
                        /// '2' and '4' followed by a swap of elements '2' and
                        /// '5' thenceforth modifying the structure to become:
                        ///
                        /// ```
                        ///   4
                        ///  / \
                        /// 1  5
                        ///   / \
                        ///  3
                        /// ```
                        fn setup() -> AdelsonVelsoLandis<usize> {
                            let mut instance = AdelsonVelsoLandis::default();

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

                            assert_eq!(root.element, 4);
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

                            assert_eq!(right.element, 5);
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
                        fn setup() -> AdelsonVelsoLandis<usize> {
                            let mut instance = AdelsonVelsoLandis::default();

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
                        fn setup() -> AdelsonVelsoLandis<usize> {
                            let mut instance = AdelsonVelsoLandis::default();

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
                            fn setup() -> AdelsonVelsoLandis<usize> {
                                let mut instance = AdelsonVelsoLandis::default();

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
                            fn setup() -> AdelsonVelsoLandis<usize> {
                                let mut instance = AdelsonVelsoLandis::default();

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
                            fn setup() -> AdelsonVelsoLandis<usize> {
                                let mut instance = AdelsonVelsoLandis::default();

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
                            fn setup() -> AdelsonVelsoLandis<usize> {
                                let mut instance = AdelsonVelsoLandis::default();

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
                    ///   2     6
                    ///  / \   / \
                    /// 1     4  7
                    ///         / \
                    ///        5  8
                    /// ```
                    ///
                    /// The deletion of element '1' should invoke a
                    /// left-rotation about element '3' thenceforth
                    /// modifying the structure to become:
                    ///
                    /// ```
                    ///      6
                    ///    /   \
                    ///   3    7
                    ///  / \  / \
                    /// 2  4 5  8
                    /// ```
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        let mut instance = AdelsonVelsoLandis::default();

                        assert!(instance.insert(3).is_ok());

                        assert!(instance.insert(2).is_ok());
                        assert!(instance.insert(6).is_ok());

                        assert!(instance.insert(1).is_ok());

                        assert!(instance.insert(4).is_ok());
                        assert!(instance.insert(7).is_ok());

                        assert!(instance.insert(5).is_ok());
                        assert!(instance.insert(8).is_ok());

                        assert_eq!(instance.remove(&1), Some(1));

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 6);
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
                    ///     3
                    ///   /   \
                    ///  1     6
                    /// / \   / \
                    ///   2  4  7
                    ///        / \
                    ///       5  8
                    /// ```
                    ///
                    /// The deletion of element '2' should invoke a
                    /// left-rotation about element '3' thenceforth
                    /// modifying the structure to become:
                    ///
                    /// ```
                    ///      6
                    ///    /   \
                    ///   3    7
                    ///  / \  / \
                    /// 1  2 5  8
                    /// ```
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        let mut instance = AdelsonVelsoLandis::default();

                        assert!(instance.insert(3).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(6).is_ok());

                        assert!(instance.insert(2).is_ok());

                        assert!(instance.insert(4).is_ok());
                        assert!(instance.insert(7).is_ok());

                        assert!(instance.insert(5).is_ok());
                        assert!(instance.insert(8).is_ok());

                        assert_eq!(instance.remove(&2), Some(2));

                        instance
                    }

                    #[test]
                    fn root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 6);
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
                    ///   3      8
                    ///  / \    / \
                    /// 1  4   7
                    ///   / \
                    ///  2  5
                    /// ```
                    ///
                    /// The deletion of element '7' should invoke a
                    /// left-rotation about element '3' followed by a
                    /// right-rotation about element '6' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      4
                    ///    /   \
                    ///   3    6
                    ///  / \  / \
                    /// 1  2 5  8
                    /// ```
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        let mut instance = AdelsonVelsoLandis::default();

                        assert!(instance.insert(6).is_ok());

                        assert!(instance.insert(3).is_ok());
                        assert!(instance.insert(8).is_ok());

                        assert!(instance.insert(1).is_ok());
                        assert!(instance.insert(4).is_ok());

                        assert!(instance.insert(7).is_ok());

                        assert!(instance.insert(2).is_ok());
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
                        todo!()
                    }

                    #[test]
                    fn left_left_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn left_right_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn right_child() {
                        todo!()
                    }

                    #[test]
                    fn right_left_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn right_right_grandchild() {
                        todo!()
                    }
                }

                mod when_leaf_is_right_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///      6
                    ///    /   \
                    ///   3    7
                    ///  / \  / \
                    /// 1  4    8
                    ///   / \
                    ///  2  5
                    /// ```
                    ///
                    /// The deletion of element '8' should invoke a
                    /// left-rotation about element '3' followed by a
                    /// right-rotation about element '6' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      4
                    ///    /   \
                    ///   3    6
                    ///  / \  / \
                    /// 1  2 5  7
                    /// ```
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        todo!()
                    }

                    #[test]
                    fn root() {
                        todo!()
                    }

                    #[test]
                    fn left_child() {
                        todo!()
                    }

                    #[test]
                    fn left_left_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn left_right_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn right_child() {
                        todo!()
                    }

                    #[test]
                    fn right_left_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn right_right_grandchild() {
                        todo!()
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
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        todo!()
                    }

                    #[test]
                    fn root() {
                        todo!()
                    }

                    #[test]
                    fn left_child() {
                        todo!()
                    }

                    #[test]
                    fn left_left_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn left_right_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn right_child() {
                        todo!()
                    }

                    #[test]
                    fn right_left_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn right_right_grandchild() {
                        todo!()
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
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        todo!()
                    }

                    #[test]
                    fn root() {
                        todo!()
                    }

                    #[test]
                    fn left_child() {
                        todo!()
                    }

                    #[test]
                    fn left_left_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn left_right_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn right_child() {
                        todo!()
                    }

                    #[test]
                    fn right_left_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn right_right_grandchild() {
                        todo!()
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
                    ///       4
                    ///    /    \
                    ///   2     7
                    ///  / \   / \
                    /// 1     5  8
                    ///      / \
                    ///     3  6
                    /// ```
                    ///
                    /// The deletion of element '1' should invoke a
                    /// right-rotation about element '7' followed by a
                    /// left-rotation about element '4' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      5
                    ///    /   \
                    ///   4    7
                    ///  / \  / \
                    /// 2  3 6  8
                    /// ```
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        todo!()
                    }

                    #[test]
                    fn root() {
                        todo!()
                    }

                    #[test]
                    fn left_child() {
                        todo!()
                    }

                    #[test]
                    fn left_left_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn left_right_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn right_child() {
                        todo!()
                    }

                    #[test]
                    fn right_left_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn right_right_grandchild() {
                        todo!()
                    }
                }

                mod when_leaf_is_right_child {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///      4
                    ///   /    \
                    ///  1     7
                    /// / \   / \
                    ///   2  5  8
                    ///     / \
                    ///    3  6
                    /// ```
                    ///
                    /// The deletion of element '2' should invoke a
                    /// right-rotation about element '7' followed by a
                    /// left-rotation about element '4' thenceforth modifying
                    /// the structure to become:
                    ///
                    /// ```
                    ///      5
                    ///    /   \
                    ///   4    7
                    ///  / \  / \
                    /// 1  3 6  8
                    /// ```
                    fn setup() -> AdelsonVelsoLandis<usize> {
                        todo!()
                    }

                    #[test]
                    fn root() {
                        todo!()
                    }

                    #[test]
                    fn left_child() {
                        todo!()
                    }

                    #[test]
                    fn left_left_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn left_right_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn right_child() {
                        todo!()
                    }

                    #[test]
                    fn right_left_grandchild() {
                        todo!()
                    }

                    #[test]
                    fn right_right_grandchild() {
                        todo!()
                    }
                }
            }
        }
    }

    mod default {
        use super::*;

        #[test]
        fn is_empty() {
            let instance = AdelsonVelsoLandis::<usize>::default();

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
                let instance = AdelsonVelsoLandis::<usize>::from_iter(core::iter::empty());

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
