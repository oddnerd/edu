//! Implementation of [`AdelsonVelskyLandis`].

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
                            unsafe { ancestor.as_mut() }.left = Some(Node::rotate_right(child));
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

        // TODO: reconsider
        right_node.balance = match (right_node.left, right_node.right) {
            (Some(_), Some(_)) => BalanceFactor::Balanced,
            (None, None | Some(_)) => unreachable!("old root should become the left child"),
            (Some(_), None) => unreachable!("logic error to rotate when not imbalanced"),
        };

        // TODO: reconsider
        root_node.balance = match (root_node.left, root_node.right) {
            (Some(_), Some(_)) | (None, None) => BalanceFactor::Balanced,
            (Some(_), None) | (None, Some(_)) => unreachable!("logic error to rotate when not imbalanced"),
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

        // TODO: reconsider
        left_node.balance = match (left_node.left, left_node.right) {
            (Some(_), Some(_)) => BalanceFactor::Balanced,
            (None | Some(_), None) => unreachable!("old root should become the right child"),
            (None, Some(_)) => unreachable!("logic error to rotate when not imbalanced"),
        };

        // TODO: reconsider
        root_node.balance = match (root_node.left, root_node.right) {
            (Some(_), Some(_)) | (None, None) => BalanceFactor::Balanced,
            (Some(_), None) | (None, Some(_)) => unreachable!("logic error to rotate when not imbalanced"),
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

                assert!(instance.insert(0).is_ok_and(|inserted| {
                    inserted == &0
                }));

                // SAFETY: no other reference exists to this node to alias.
                let root = unsafe { instance.root.unwrap().as_ref() };

                assert_eq!(root.element, 0);
                assert_eq!(root.balance, BalanceFactor::Balanced);
                assert_eq!(root.parent, None);
                assert_eq!(root.left, None);
                assert_eq!(root.right, None);
            }

            mod no_rotation {
                use super::*;

                mod when_left_of_root {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///    0
                    ///   / \
                    /// -1
                    /// ```
                    fn setup() -> AdelsonVelsoLandis<i32> {
                        let mut instance = AdelsonVelsoLandis::<i32>::default();

                        // The root value.
                        assert!(instance.insert(0).is_ok());

                        // The value less than the root being tested.
                        assert!(instance.insert(-1).is_ok_and(|inserted| {
                            inserted == &-1
                        }));

                        instance
                    }

                    #[test]
                    fn updates_root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 0);
                        assert_eq!(root.balance, BalanceFactor::Left);
                        assert_eq!(root.parent, None);
                        assert!(root.left.is_some());
                        assert_eq!(root.right, None);
                    }

                    #[test]
                    fn initializes_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let left = unsafe { root.left.unwrap().as_ref() };

                        assert_eq!(left.element, -1);
                        assert_eq!(left.balance, BalanceFactor::Balanced);
                        assert_eq!(left.parent, Some(root_ptr));
                        assert_eq!(left.left, None);
                        assert_eq!(left.right, None);
                    }
                }

                mod when_right_of_root {
                    use super::*;

                    /// Should create the following structure:
                    ///
                    /// ```
                    ///  0
                    /// / \
                    ///   1
                    /// ```
                    fn setup() -> AdelsonVelsoLandis<i32> {
                        let mut instance = AdelsonVelsoLandis::<i32>::default();

                        // The root value.
                        assert!(instance.insert(0).is_ok());

                        // The value greater than the root being tested.
                        assert!(instance.insert(1).is_ok_and(|inserted| {
                            inserted == &1
                        }));

                        instance
                    }

                    #[test]
                    fn updates_root() {
                        let instance = setup();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { instance.root.unwrap().as_ref() };

                        assert_eq!(root.element, 0);
                        assert_eq!(root.balance, BalanceFactor::Right);
                        assert_eq!(root.parent, None);
                        assert_eq!(root.left, None);
                        assert!(root.right.is_some());
                    }

                    #[test]
                    fn initializes_child() {
                        let instance = setup();

                        let root_ptr = instance.root.unwrap();

                        // SAFETY: no other reference exists to this node to alias.
                        let root = unsafe { root_ptr.as_ref() };

                        // SAFETY: no other reference exists to this node to alias.
                        let right = unsafe { root.right.unwrap().as_ref() };

                        assert_eq!(right.element, 1);
                        assert_eq!(right.balance, BalanceFactor::Balanced);
                        assert_eq!(right.parent, Some(root_ptr));
                        assert_eq!(right.left, None);
                        assert_eq!(right.right, None);
                    }
                }

                mod when_extending_balanced_tree {
                    use super::*;

                    mod to_the_left {
                        use super::*;

                        /// Should create the following structure:
                        ///
                        /// ```
                        ///      0
                        ///     / \
                        ///   -2  1
                        ///   / \
                        /// -3  -1
                        /// ```
                        fn setup() -> AdelsonVelsoLandis<i32> {
                            let mut instance = AdelsonVelsoLandis::<i32>::default();

                            // The root node.
                            assert!(instance.insert(0).is_ok_and(|inserted| inserted == &0));

                            // Children of the root.
                            assert!(instance.insert(-2).is_ok_and(|inserted| inserted == &-2));
                            assert!(instance.insert(1).is_ok_and(|inserted| inserted == &1));

                            // Children of the right child.
                            assert!(instance.insert(-3).is_ok_and(|inserted| inserted == &-3));
                            assert!(instance.insert(-1).is_ok_and(|inserted| inserted == &-1));

                            instance
                        }

                        #[test]
                        fn updates_root() {
                            let instance = setup();

                            // SAFETY: no other reference to this node exist to alias.
                            let root = unsafe { instance.root.unwrap().as_ref() };

                            assert_eq!(root.element, 0);
                            assert_eq!(root.balance, BalanceFactor::Left);
                            assert_eq!(root.parent, None);
                            assert!(root.left.is_some());
                            assert!(root.right.is_some());
                        }

                        #[test]
                        fn updates_left_child() {
                            let instance = setup();

                            let root_ptr = instance.root.unwrap();

                            // SAFETY: no other reference to this node exist to alias.
                            let root = unsafe { root_ptr.as_ref() };

                            // SAFETY: no other reference to this node exist to alias.
                            let left = unsafe { root.left.unwrap().as_ref() };

                            assert_eq!(left.element, -2);
                            assert_eq!(left.balance, BalanceFactor::Balanced);
                            assert_eq!(left.parent, Some(root_ptr));
                            assert!(left.left.is_some());
                            assert!(left.right.is_some());
                        }

                        #[test]
                        fn does_not_modify_right_child() {
                            let instance = setup();

                            let root_ptr = instance.root.unwrap();

                            // SAFETY: no other reference to this node exist to alias.
                            let root = unsafe { root_ptr.as_ref() };

                            // SAFETY: no other reference to this node exist to alias.
                            let right = unsafe { root.right.unwrap().as_ref() };

                            assert_eq!(right.element, 1);
                            assert_eq!(right.balance, BalanceFactor::Balanced);
                            assert_eq!(right.parent, Some(root_ptr));
                            assert_eq!(right.left, None);
                            assert_eq!(right.right, None);
                        }

                        #[test]
                        fn initializes_left_grandchild() {
                            let instance = setup();

                            // SAFETY: no other reference to this node exist to alias.
                            let root = unsafe { instance.root.unwrap().as_ref() };

                            let left_ptr = root.left.unwrap();

                            // SAFETY: no other reference to this node exist to alias.
                            let left = unsafe { left_ptr.as_ref() };

                            // SAFETY: no other reference to this node exist to alias.
                            let left_left = unsafe { left.left.unwrap().as_ref() };

                            assert_eq!(left_left.element, -3);
                            assert_eq!(left_left.balance, BalanceFactor::Balanced);
                            assert_eq!(left_left.parent, Some(left_ptr));
                            assert_eq!(left_left.left, None);
                            assert_eq!(left_left.right, None);
                        }

                        #[test]
                        fn initializes_right_grandchild() {
                            let instance = setup();

                            // SAFETY: no other reference to this node exist to alias.
                            let root = unsafe { instance.root.unwrap().as_ref() };

                            let left_ptr = root.left.unwrap();

                            // SAFETY: no other reference to this node exist to alias.
                            let left = unsafe { left_ptr.as_ref() };

                            // SAFETY: no other reference to this node exist to alias.
                            let left_right = unsafe { left.right.unwrap().as_ref() };

                            assert_eq!(left_right.element, -1);
                            assert_eq!(left_right.balance, BalanceFactor::Balanced);
                            assert_eq!(left_right.parent, Some(left_ptr));
                            assert_eq!(left_right.left, None);
                            assert_eq!(left_right.right, None);
                        }
                    }

                    mod to_the_right {
                        use super::*;

                        /// Should create the following structure:
                        ///
                        /// ```
                        ///    0
                        ///   / \
                        /// -1  2
                        ///    / \
                        ///   1  3
                        /// ```
                        fn setup() -> AdelsonVelsoLandis<i32> {
                            let mut instance = AdelsonVelsoLandis::<i32>::default();

                            // The root node.
                            assert!(instance.insert(0).is_ok_and(|inserted| inserted == &0));

                            // Children of the root.
                            assert!(instance.insert(-1).is_ok_and(|inserted| inserted == &-1));
                            assert!(instance.insert(2).is_ok_and(|inserted| inserted == &2));

                            // Children of the right child.
                            assert!(instance.insert(1).is_ok_and(|inserted| inserted == &1));
                            assert!(instance.insert(3).is_ok_and(|inserted| inserted == &3));

                            instance
                        }

                        #[test]
                        fn updates_root() {
                            let instance = setup();

                            // SAFETY: no other reference to this node exist to alias.
                            let root = unsafe { instance.root.unwrap().as_ref() };

                            assert_eq!(root.element, 0);
                            assert_eq!(root.balance, BalanceFactor::Right);
                            assert_eq!(root.parent, None);
                            assert!(root.left.is_some());
                            assert!(root.right.is_some());
                        }

                        #[test]
                        fn does_not_modify_left_child() {
                            let instance = setup();

                            let root_ptr = instance.root.unwrap();

                            // SAFETY: no other reference to this node exist to alias.
                            let root = unsafe { root_ptr.as_ref() };

                            // SAFETY: no other reference to this node exist to alias.
                            let left = unsafe { root.left.unwrap().as_ref() };

                            assert_eq!(left.element, -1);
                            assert_eq!(left.balance, BalanceFactor::Balanced);
                            assert_eq!(left.parent, Some(root_ptr));
                            assert_eq!(left.left, None);
                            assert_eq!(left.right, None);
                        }

                        #[test]
                        fn updates_right_child() {
                            let instance = setup();

                            let root_ptr = instance.root.unwrap();

                            // SAFETY: no other reference to this node exist to alias.
                            let root = unsafe { root_ptr.as_ref() };

                            // SAFETY: no other reference to this node exist to alias.
                            let right = unsafe { root.right.unwrap().as_ref() };

                            assert_eq!(right.element, 2);
                            assert_eq!(right.balance, BalanceFactor::Balanced);
                            assert_eq!(right.parent, Some(root_ptr));
                            assert!(right.left.is_some());
                            assert!(right.right.is_some());
                        }

                        #[test]
                        fn initializes_left_grandchild() {
                            let instance = setup();

                            // SAFETY: no other reference to this node exist to alias.
                            let root = unsafe { instance.root.unwrap().as_ref() };

                            let right_ptr = root.right.unwrap();

                            // SAFETY: no other reference to this node exist to alias.
                            let right = unsafe { right_ptr.as_ref() };

                            // SAFETY: no other reference to this node exist to alias.
                            let right_left = unsafe { right.left.unwrap().as_ref() };

                            assert_eq!(right_left.element, 1);
                            assert_eq!(right_left.balance, BalanceFactor::Balanced);
                            assert_eq!(right_left.parent, Some(right_ptr));
                            assert_eq!(right_left.left, None);
                            assert_eq!(right_left.right, None);
                        }

                        #[test]
                        fn initializes_right_grandchild() {
                            let instance = setup();

                            // SAFETY: no other reference to this node exist to alias.
                            let root = unsafe { instance.root.unwrap().as_ref() };

                            let right_ptr = root.right.unwrap();

                            // SAFETY: no other reference to this node exist to alias.
                            let right = unsafe { right_ptr.as_ref() };

                            // SAFETY: no other reference to this node exist to alias.
                            let right_right = unsafe { right.right.unwrap().as_ref() };

                            assert_eq!(right_right.element, 3);
                            assert_eq!(right_right.balance, BalanceFactor::Balanced);
                            assert_eq!(right_right.parent, Some(right_ptr));
                            assert_eq!(right_right.left, None);
                            assert_eq!(right_right.right, None);
                        }
                    }
                }
            }

            mod left_rotation {
                use super::*;

                /// Should create the following structure:
                ///
                /// ```
                ///    0
                ///   / \
                /// -1  2
                ///    / \
                ///   1  3
                ///       \
                ///       4
                /// ```
                ///
                /// which should invoke a left-rotation becoming:
                ///
                /// ```
                ///      2
                ///     / \
                ///    0  3
                ///   / \  \
                /// -1  1  4
                /// ```
                fn setup() -> AdelsonVelsoLandis<i32> {
                    let mut instance = AdelsonVelsoLandis::<i32>::default();

                    // The root node.
                    assert!(instance.insert(0).is_ok_and(|inserted| inserted == &0));

                    // Children of the root.
                    assert!(instance.insert(-1).is_ok_and(|inserted| inserted == &-1));
                    assert!(instance.insert(2).is_ok_and(|inserted| inserted == &2));

                    // Children of the right child.
                    assert!(instance.insert(1).is_ok_and(|inserted| inserted == &1));
                    assert!(instance.insert(3).is_ok_and(|inserted| inserted == &3));

                    // This insertion triggers a left-rotation.
                    assert!(instance.insert(4).is_ok_and(|inserted| inserted == &4));

                    instance
                }

                #[test]
                fn updates_root() {
                    let instance = setup();

                    // SAFETY: no other reference to this node exist to alias.
                    let root = unsafe { instance.root.unwrap().as_ref() };

                    assert_eq!(root.element, 2);
                    assert_eq!(root.balance, BalanceFactor::Balanced);
                    assert_eq!(root.parent, None);
                    assert!(root.left.is_some());
                    assert!(root.right.is_some());
                }

                #[test]
                fn updates_left_child() {
                    let instance = setup();

                    let root_ptr = instance.root.unwrap();

                    // SAFETY: no other reference to this node exist to alias.
                    let root = unsafe { root_ptr.as_ref() };

                    // SAFETY: no other reference to this node exist to alias.
                    let left = unsafe { root.left.unwrap().as_ref() };

                    assert_eq!(left.element, 0);
                    assert_eq!(left.balance, BalanceFactor::Balanced);
                    assert_eq!(left.parent, Some(root_ptr));
                    assert!(left.left.is_some());
                    assert!(left.right.is_some());
                }

                #[test]
                fn updates_left_left_grandchild() {
                    let instance = setup();

                    // SAFETY: no other reference to this node exist to alias.
                    let root = unsafe { instance.root.unwrap().as_ref() };

                    let left_ptr = root.left.unwrap();

                    // SAFETY: no other reference to this node exist to alias.
                    let left = unsafe { left_ptr.as_ref() };

                    // SAFETY: no other reference to this node exist to alias.
                    let left_left = unsafe { left.left.unwrap().as_ref() };

                    assert_eq!(left_left.element, -1);
                    assert_eq!(left_left.balance, BalanceFactor::Balanced);
                    assert_eq!(left_left.parent, Some(left_ptr));
                    assert_eq!(left_left.left, None);
                    assert_eq!(left_left.right, None);
                }

                #[test]
                fn updates_left_right_grandchild() {
                    let instance = setup();

                    // SAFETY: no other reference to this node exist to alias.
                    let root = unsafe { instance.root.unwrap().as_ref() };

                    let left_ptr = root.left.unwrap();

                    // SAFETY: no other reference to this node exist to alias.
                    let left = unsafe { left_ptr.as_ref() };

                    // SAFETY: no other reference to this node exist to alias.
                    let left_right = unsafe { left.right.unwrap().as_ref() };

                    assert_eq!(left_right.element, 1);
                    assert_eq!(left_right.balance, BalanceFactor::Balanced);
                    assert_eq!(left_right.parent, Some(left_ptr));
                    assert_eq!(left_right.left, None);
                    assert_eq!(left_right.right, None);
                }

                #[test]
                fn updates_right_child() {
                    let instance = setup();

                    let root_ptr = instance.root.unwrap();

                    // SAFETY: no other reference to this node exist to alias.
                    let root = unsafe { root_ptr.as_ref() };

                    // SAFETY: no other reference to this node exist to alias.
                    let right = unsafe { root.right.unwrap().as_ref() };

                    assert_eq!(right.element, 3);
                    assert_eq!(right.balance, BalanceFactor::Right);
                    assert_eq!(right.parent, Some(root_ptr));
                    assert_eq!(right.left, None);
                    assert!(right.right.is_some());
                }

                #[test]
                fn updates_right_grandchild() {
                    let instance = setup();

                    // SAFETY: no other reference to this node exist to alias.
                    let root = unsafe { instance.root.unwrap().as_ref() };

                    let right_ptr = root.right.unwrap();

                    // SAFETY: no other reference to this node exist to alias.
                    let right = unsafe { right_ptr.as_ref() };

                    // SAFETY: no other reference to this node exist to alias.
                    let right_right = unsafe { right.right.unwrap().as_ref() };

                    assert_eq!(right_right.element, 4);
                    assert_eq!(right_right.balance, BalanceFactor::Balanced);
                    assert_eq!(right_right.parent, Some(right_ptr));
                    assert_eq!(right_right.left, None);
                    assert_eq!(right_right.right, None);
                }
            }

            mod right_rotation {
                use super::*;

                /// Should create the following structure:
                ///
                /// ```
                ///       5
                ///      / \
                ///     3  6
                ///    / \
                ///   2  4
                ///  /
                /// 1
                /// ```
                ///
                /// which should invoke a right-rotation becoming:
                ///
                /// ```
                ///     3
                ///    / \
                ///   2  5
                ///  /  / \
                /// 1  4  6
                /// ```
                fn setup() -> AdelsonVelsoLandis<i32> {
                    let mut instance = AdelsonVelsoLandis::<i32>::default();

                    // The root node.
                    assert!(instance.insert(5).is_ok_and(|inserted| inserted == &5));

                    // Children of the root.
                    assert!(instance.insert(3).is_ok_and(|inserted| inserted == &3));
                    assert!(instance.insert(6).is_ok_and(|inserted| inserted == &6));

                    // Children of the left child.
                    assert!(instance.insert(2).is_ok_and(|inserted| inserted == &2));
                    assert!(instance.insert(4).is_ok_and(|inserted| inserted == &4));

                    // This insertion triggers a right-rotation.
                    assert!(instance.insert(1).is_ok_and(|inserted| inserted == &1));

                    instance
                }

                #[test]
                fn updates_root() {
                    let instance = setup();

                    // SAFETY: no other reference to this node exist to alias.
                    let root = unsafe { instance.root.unwrap().as_ref() };

                    assert_eq!(root.element, 3);
                    assert_eq!(root.balance, BalanceFactor::Balanced);
                    assert_eq!(root.parent, None);
                    assert!(root.left.is_some());
                    assert!(root.right.is_some());
                }

                #[test]
                fn updates_left_child() {
                    let instance = setup();

                    let root_ptr = instance.root.unwrap();

                    // SAFETY: no other reference to this node exist to alias.
                    let root = unsafe { root_ptr.as_ref() };

                    // SAFETY: no other reference to this node exist to alias.
                    let left = unsafe { root.left.unwrap().as_ref() };

                    assert_eq!(left.element, 2);
                    assert_eq!(left.balance, BalanceFactor::Left);
                    assert_eq!(left.parent, Some(root_ptr));
                    assert!(left.left.is_some());
                    assert_eq!(left.right, None);
                }

                #[test]
                fn updates_left_grandchild() {
                    let instance = setup();

                    // SAFETY: no other reference to this node exist to alias.
                    let root = unsafe { instance.root.unwrap().as_ref() };

                    let left_ptr = root.left.unwrap();

                    // SAFETY: no other reference to this node exist to alias.
                    let left = unsafe { left_ptr.as_ref() };

                    // SAFETY: no other reference to this node exist to alias.
                    let left_left = unsafe { left.left.unwrap().as_ref() };

                    assert_eq!(left_left.element, 1);
                    assert_eq!(left_left.balance, BalanceFactor::Balanced);
                    assert_eq!(left_left.parent, Some(left_ptr));
                    assert_eq!(left_left.left, None);
                    assert_eq!(left_left.right, None);
                }

                #[test]
                fn updates_right_child() {
                    let instance = setup();

                    let root_ptr = instance.root.unwrap();

                    // SAFETY: no other reference to this node exist to alias.
                    let root = unsafe { root_ptr.as_ref() };

                    // SAFETY: no other reference to this node exist to alias.
                    let right = unsafe { root.right.unwrap().as_ref() };

                    assert_eq!(right.element, 5);
                    assert_eq!(right.balance, BalanceFactor::Balanced);
                    assert_eq!(right.parent, Some(root_ptr));
                    assert!(right.left.is_some());
                    assert!(right.right.is_some());
                }

                #[test]
                fn updates_right_left_grandchild() {
                    let instance = setup();

                    // SAFETY: no other reference to this node exist to alias.
                    let root = unsafe { instance.root.unwrap().as_ref() };

                    let right_ptr = root.right.unwrap();

                    // SAFETY: no other reference to this node exist to alias.
                    let right = unsafe { right_ptr.as_ref() };

                    // SAFETY: no other reference to this node exist to alias.
                    let right_left = unsafe { right.left.unwrap().as_ref() };

                    assert_eq!(right_left.element, 4);
                    assert_eq!(right_left.balance, BalanceFactor::Balanced);
                    assert_eq!(right_left.parent, Some(right_ptr));
                    assert_eq!(right_left.left, None);
                    assert_eq!(right_left.right, None);
                }

                #[test]
                fn updates_right_right_grandchild() {
                    let instance = setup();

                    // SAFETY: no other reference to this node exist to alias.
                    let root = unsafe { instance.root.unwrap().as_ref() };

                    let right_ptr = root.right.unwrap();

                    // SAFETY: no other reference to this node exist to alias.
                    let right = unsafe { right_ptr.as_ref() };

                    // SAFETY: no other reference to this node exist to alias.
                    let right_right = unsafe { right.right.unwrap().as_ref() };

                    assert_eq!(right_right.element, 6);
                    assert_eq!(right_right.balance, BalanceFactor::Balanced);
                    assert_eq!(right_right.parent, Some(right_ptr));
                    assert_eq!(right_right.left, None);
                    assert_eq!(right_right.right, None);
                }
            }
        }

        mod remove {
            use super::*;

            #[test]
            fn when_empty() {
                let mut instance = AdelsonVelsoLandis::<i32>::default();

                assert_eq!(instance.remove(&0), None);
            }

            #[test]
            fn when_not_contained() {
                let mut instance = AdelsonVelsoLandis::<i32>::default();

                // TODO: use FromIterator or similar.
                assert!(instance.insert(0).is_ok());
                assert!(instance.insert(1).is_ok());
                assert!(instance.insert(2).is_ok());
                assert!(instance.insert(3).is_ok());
                assert!(instance.insert(4).is_ok());
                assert!(instance.insert(5).is_ok());

                assert_eq!(instance.remove(&6), None);
            }

            mod no_rotation {
                use super::*;
            }

            mod left_rotation {
                use super::*;
            }

            mod right_rotation {
                use super::*;
            }
        }
    }
}
