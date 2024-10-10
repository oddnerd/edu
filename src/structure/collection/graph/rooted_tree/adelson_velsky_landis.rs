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
    /// TODO
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

        let Some(mut right) = root_node.right.take() else {
            panic!("it is a logic error to rotate left without a right child");
        };

        // SAFETY: no other reference to this node exists to alias.
        let right_node = unsafe { right.as_mut() };

        if let Some(mut right_left) = right_node.left.take() {
            // SAFETY: no other reference to this node exists to alias.
            let right_left_node = unsafe { right_left.as_mut() };

            right_left_node.parent = Some(root);
            root_node.right = Some(right_left);
        }

        core::mem::swap(&mut root_node.parent, &mut right_node.parent);
        right_node.left = Some(root);

        right
    }

    /// TODO
    fn rotate_right(mut root: core::ptr::NonNull<Self>) -> core::ptr::NonNull<Self> {
        // SAFETY: no other reference to this node exists to alias.
        let root_node = unsafe { root.as_mut() };

        let Some(mut left) = root_node.left.take() else {
            panic!("it is a logic error to rotate left without a right child");
        };

        // SAFETY: no other reference to this node exists to alias.
        let left_node = unsafe { left.as_mut() };

        if let Some(mut left_right) = left_node.right.take() {
            // SAFETY: no other reference to this node exists to alias.
            let left_right_node = unsafe { left_right.as_mut() };

            left_right_node.parent = Some(root);
            root_node.left = Some(left_right);
        }

        core::mem::swap(&mut root_node.parent, &mut left_node.parent);
        left_node.right = Some(root);

        left
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

            #[test]
            fn descends_left_branch_when_less() {
                let mut instance = AdelsonVelsoLandis::<i32>::default();

                // The root value.
                assert!(instance.insert(0).is_ok());

                // The value less than the root being tested.
                assert!(instance.insert(-1).is_ok_and(|inserted| {
                    inserted == & -1
                }));

                let root_ptr = instance.root.unwrap();

                // SAFETY: no other reference exists to this node to alias.
                let root = unsafe { root_ptr.as_ref() };

                assert_eq!(root.element, 0);
                assert_eq!(root.balance, BalanceFactor::Left);
                assert_eq!(root.parent, None);
                assert_eq!(root.right, None);

                // SAFETY: no other reference exists to this node to alias.
                let left = unsafe { root.left.unwrap().as_ref() };

                assert_eq!(left.element, -1);
                assert_eq!(left.balance, BalanceFactor::Balanced);
                assert_eq!(left.parent, Some(root_ptr));
                assert_eq!(left.left, None);
                assert_eq!(left.right, None);
            }

            #[test]
            fn descends_right_branch_when_greater() {
                let mut instance = AdelsonVelsoLandis::<i32>::default();

                // The root value.
                assert!(instance.insert(0).is_ok());

                // The value less than the root being tested.
                assert!(instance.insert(1).is_ok_and(|inserted| {
                    inserted == & 1
                }));

                let root_ptr = instance.root.unwrap();

                // SAFETY: no other reference exists to this node to alias.
                let root = unsafe { root_ptr.as_ref() };

                assert_eq!(root.element, 0);
                assert_eq!(root.balance, BalanceFactor::Right);
                assert_eq!(root.parent, None);
                assert_eq!(root.left, None);

                // SAFETY: no other reference exists to this node to alias.
                let right = unsafe { root.right.unwrap().as_ref() };

                assert_eq!(right.element, 1);
                assert_eq!(right.balance, BalanceFactor::Balanced);
                assert_eq!(right.parent, Some(root_ptr));
                assert_eq!(right.left, None);
                assert_eq!(right.right, None);
            }

            #[test]
            #[allow(clippy::cognitive_complexity, reason = "checks each node")]
            fn does_no_rotation_when_insertion_order_self_balances() {
                // The following order-sensitive insertions create the
                // depicted graph:
                //
                //    0
                //   / \
                // -1  2
                //    / \
                //   1  3
                //
                // Although the right branch is longer than the left, the
                // balance factor is at most one after each insertion hence
                // no rotation would perfectly balance the tree, so the
                // expected result is no left/right rotation occurs.

                let mut instance = AdelsonVelsoLandis::<i32>::default();

                // The root node.
                assert!(instance.insert(0).is_ok_and(|inserted| inserted == &0));

                // Children of the root.
                assert!(instance.insert(-1).is_ok_and(|inserted| inserted == &-1));
                assert!(instance.insert(2).is_ok_and(|inserted| inserted == &2));

                // Children of the right child.
                assert!(instance.insert(1).is_ok_and(|inserted| inserted == &1));
                assert!(instance.insert(3).is_ok_and(|inserted| inserted == &3));

                let root_ptr = instance.root.unwrap();

                // SAFETY: no other reference to this node exist to alias.
                let root = unsafe { root_ptr.as_ref() };

                assert_eq!(root.element, 0);
                assert_eq!(root.balance, BalanceFactor::Right);
                assert_eq!(root.parent, None);

                // SAFETY: no other reference to this node exist to alias.
                let left = unsafe { root.left.unwrap().as_ref() };

                assert_eq!(left.element, -1);
                assert_eq!(left.balance, BalanceFactor::Balanced);
                assert_eq!(left.parent, Some(root_ptr));
                assert_eq!(left.left, None);
                assert_eq!(left.right, None);

                let right_ptr = root.right.unwrap();

                // SAFETY: no other reference to this node exist to alias.
                let right = unsafe { right_ptr.as_ref() };

                assert_eq!(right.element, 2);
                assert_eq!(right.balance, BalanceFactor::Balanced);
                assert_eq!(right.parent, Some(root_ptr));

                // SAFETY: no other reference to this node exist to alias.
                let right_left = unsafe { right.left.unwrap().as_ref() };

                assert_eq!(right_left.element, 1);
                assert_eq!(right_left.balance, BalanceFactor::Balanced);
                assert_eq!(right_left.parent, Some(right_ptr));
                assert_eq!(right_left.left, None);
                assert_eq!(right_left.right, None);

                // SAFETY: no other reference to this node exist to alias.
                let right_right = unsafe { right.right.unwrap().as_ref() };

                assert_eq!(right_right.element, 3);
                assert_eq!(right_right.balance, BalanceFactor::Balanced);
                assert_eq!(right_right.parent, Some(right_ptr));
                assert_eq!(right_right.left, None);
                assert_eq!(right_right.right, None);
            }

            #[test]
            #[allow(clippy::cognitive_complexity, reason = "checks each node")]
            fn does_left_rotation_when_right_right_imbalance() {
                let mut instance = AdelsonVelsoLandis::<i32>::default();

                // The following order-sensitive insertions create the
                // depicted graph:
                //
                //    0
                //   / \
                // -1  2
                //    / \
                //   1  3
                //       \
                //       4
                //
                // This causes an imbalance where the right branch with nodes
                // '0 -> 2 -> 3 -> 4' has height three whereas the left branch
                // with nodes '0 -> -1' has height one, an imbalance of two,
                // thereby requiring a left-rotation about the root. Note that
                // the elements are inserted such that the imbalance occurs
                // only when the final element, 4, is inserted.

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

                // Inserting the last element should invoke a left-rotation
                // thereby balancing the tree resulting in the depicted graph:
                //
                //       2
                //      / \
                //     0  3
                //    / \  \
                //  -1  1  4

                let root_ptr = instance.root.unwrap();

                // SAFETY: no other reference to this node exist to alias.
                let root = unsafe { root_ptr.as_ref() };

                assert_eq!(root.element, 2);
                assert_eq!(root.balance, BalanceFactor::Balanced);
                assert_eq!(root.parent, None);

                let left_ptr = root.left.unwrap();

                // SAFETY: no other reference to this node exist to alias.
                let left = unsafe { left_ptr.as_ref() };

                assert_eq!(left.element, 0);
                assert_eq!(left.balance, BalanceFactor::Balanced);
                assert_eq!(left.parent, Some(root_ptr));

                // SAFETY: no other reference to this node exist to alias.
                let left_left = unsafe { left.left.unwrap().as_ref() };

                assert_eq!(left_left.element, -1);
                assert_eq!(left_left.balance, BalanceFactor::Balanced);
                assert_eq!(left_left.parent, Some(left_ptr));
                assert_eq!(left_left.left, None);
                assert_eq!(left_left.right, None);

                // SAFETY: no other reference to this node exist to alias.
                let left_right = unsafe { left.right.unwrap().as_ref() };

                assert_eq!(left_right.element, 1);
                assert_eq!(left_right.balance, BalanceFactor::Balanced);
                assert_eq!(left_right.parent, Some(left_ptr));
                assert_eq!(left_right.left, None);
                assert_eq!(left_right.right, None);

                let right_ptr = root.right.unwrap();

                // SAFETY: no other reference to this node exist to alias.
                let right = unsafe { right_ptr.as_ref() };

                assert_eq!(right.element, 3);
                assert_eq!(right.balance, BalanceFactor::Right);
                assert_eq!(right.parent, Some(root_ptr));
                assert_eq!(right.left, None);

                // SAFETY: no other reference to this node exist to alias.
                let right_right = unsafe { right.right.unwrap().as_ref() };

                assert_eq!(right_right.element, 4);
                assert_eq!(right_right.balance, BalanceFactor::Balanced);
                assert_eq!(right_right.parent, Some(right_ptr));
                assert_eq!(right_right.left, None);
                assert_eq!(right_right.right, None);
            }

            #[test]
            #[allow(clippy::cognitive_complexity, reason = "checks each node")]
            fn does_right_rotation_when_left_left_imbalance() {
                let mut instance = AdelsonVelsoLandis::<i32>::default();

                // The following order-sensitive insertions create the
                // depicted graph:
                //
                //       5
                //      / \
                //     3  6
                //    / \
                //   2  4
                //  /
                // 1
                //
                // This causes an imbalance where the left branch with nodes
                // '5 -> 3 -> 2 -> 1' has height three whereas the right branch
                // with nodes '5 -> 6' has height one, an imbalance of two,
                // thereby requiring a right-rotation about the root. Note that
                // the elements are inserted such that the imbalance occurs
                // only when the final element, 1, is inserted.

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

                // Inserting the last element should invoke a right-rotation
                // thereby balancing the tree resulting in the depicted graph:
                //
                //       3
                //      / \
                //     2  5
                //    /  / \
                //   1  4  6

                let root_ptr = instance.root.unwrap();

                // SAFETY: no other reference to this node exist to alias.
                let root = unsafe { root_ptr.as_ref() };

                assert_eq!(root.element, 3);
                assert_eq!(root.balance, BalanceFactor::Balanced);
                assert_eq!(root.parent, None);

                let left_ptr = root.left.unwrap();

                // SAFETY: no other reference to this node exist to alias.
                let left = unsafe { left_ptr.as_ref() };

                assert_eq!(left.element, 2);
                assert_eq!(left.balance, BalanceFactor::Left);
                assert_eq!(left.parent, Some(root_ptr));
                assert_eq!(left.right, None);

                // SAFETY: no other reference to this node exist to alias.
                let left_left = unsafe { left.left.unwrap().as_ref() };

                assert_eq!(left_left.element, 1);
                assert_eq!(left_left.balance, BalanceFactor::Balanced);
                assert_eq!(left_left.parent, Some(left_ptr));
                assert_eq!(left_left.left, None);
                assert_eq!(left_left.right, None);

                let right_ptr = root.right.unwrap();

                // SAFETY: no other reference to this node exist to alias.
                let right = unsafe { right_ptr.as_ref() };

                assert_eq!(right.element, 5);
                assert_eq!(right.balance, BalanceFactor::Balanced);
                assert_eq!(right.parent, Some(root_ptr));

                // SAFETY: no other reference to this node exist to alias.
                let right_left = unsafe { right.left.unwrap().as_ref() };

                assert_eq!(right_left.element, 4);
                assert_eq!(right_left.balance, BalanceFactor::Balanced);
                assert_eq!(right_left.parent, Some(right_ptr));
                assert_eq!(right_left.left, None);
                assert_eq!(right_left.right, None);

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
}
