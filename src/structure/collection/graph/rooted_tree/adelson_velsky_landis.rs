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
    root: Option<Box<Node<T>>>,
}

impl<T: Ord> AdelsonVelsoLandis<T> {

    /// Add a new [`Node`] with value `element`.
    ///
    /// # Errors
    /// Yields the `element` if an equivalent one is already contained,
    /// alongside a mutable reference to the contained equivalent element.
    ///
    /// # Panics
    /// The Rust runtime might panic or otherwise abort if allocation fails.
    ///
    /// # Performance
    /// This method takes O(log N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    pub fn insert(&mut self, element: T) -> Result<(), T> {
        let (mut parent, mut previous) = {
            let mut parent = None;
            let mut branch = &mut self.root;

            while let &mut Some(ref mut node) = branch {
                parent = Some(core::ptr::NonNull::from(node.as_ref()));

                branch = match element.cmp(&node.element) {
                    core::cmp::Ordering::Less => &mut node.left,
                    core::cmp::Ordering::Greater => &mut node.right,
                    core::cmp::Ordering::Equal => return Err(element),
                };
            }

            let child = branch.insert(Box::new(Node {
                element,
                parent: (parent, core::ptr::NonNull::dangling()),
                highest_branch: BalanceFactor::Balanced,
                left: None,
                right: None,
            }));

            child.parent.1 = core::ptr::NonNull::from(&mut *child);

            (parent, core::ptr::NonNull::from(child.as_ref()))
        };

        while let Some(mut current) = parent {
            let (next, mut current) = {
                // SAFETY: no other reference exists to alias.
                let current = unsafe { current.as_mut() };

                current.parent
            };

            // SAFETY: no other reference exists to alias.
            let current = unsafe { current.as_mut() };

            if current.left.as_deref_mut().is_some_and(|left| core::ptr::from_ref(left) == previous.as_ptr()) {
                // Ascended via the left branch.

                if current.highest_branch == BalanceFactor::Left {
                    // Insertion made left branch unbalanced.

                    let Some(left) = current.left.as_mut() else {
                        unreachable!("we ascended via the left branch");
                    };

                    if left.highest_branch == BalanceFactor::Right {
                        Node::rotate_left(left);
                    }

                    Node::rotate_right(current);
                } else if current.highest_branch == BalanceFactor::Right {
                    // Insertion balanced this right-heavy node.

                    current.highest_branch = BalanceFactor::Balanced;
                    break;
                } else {
                    // No imbalance yet, propagate balance factor up ancestors.
                    current.highest_branch = BalanceFactor::Left;
                }

            } else {
                // Ascended via the right branch.

                if current.highest_branch == BalanceFactor::Right {
                    // Insertion made right branch unbalanced.

                    let Some(right) = current.right.as_mut() else {
                        unreachable!("we ascended via the right branch");
                    };

                    if right.highest_branch == BalanceFactor::Left {
                        Node::rotate_right(right);
                    }

                    Node::rotate_left(current);
                } else if current.highest_branch == BalanceFactor::Left {
                    // Insertion balanced this left-heavy node.

                    current.highest_branch = BalanceFactor::Balanced;
                    break;
                } else {
                    // No imbalance yet, propagate balance factor up ancestors.
                    current.highest_branch = BalanceFactor::Right;
                }
            }

            parent = next;
            previous = core::ptr::NonNull::from(current.as_mut());
        }

        Ok(())
    }
}

/// Which branch of a [`Node`] has the subtree with the greatest height.
#[derive(Debug, PartialEq, Eq)]
enum BalanceFactor {
    /// Both branches of this [`Node`] have the same height.
    Balanced,

    /// The left branch of this [`Node`] has height one longer than the right.
    Left,

    /// The right branch of this [`Node`] has height one longer than the left.
    Right,
}

/// An instantiated element within a [`AdelsonVelskyLandis`].
#[derive(Debug)] // TODO: manually implement this.
struct Node<T> {
    /// The underlying element.
    element: T,

    /// Which branch has the subtree with the greatest height.
    highest_branch: BalanceFactor,

    /// The parent of `self`, if any.
    parent: (Option<core::ptr::NonNull<Node<T>>>, core::ptr::NonNull<Box<Node<T>>>),

    /// The left child, if any.
    left: Option<Box<Node<T>>>,

    /// The right child, if any.
    right: Option<Box<Node<T>>>,
}

impl<T> Node<T> {
    /// TODO
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    fn rotate_left(branch: &mut Box<Node<T>>) {
        let Some(mut right) = branch.right.take() else {
            panic!(); // TODO: handle this more gracefully?
        };

        if let Some(mut right_left) = right.left.take() {
            right_left.parent = Some(core::ptr::NonNull::from(branch.as_mut()));
            branch.right = Some(right_left);
        }

        core::mem::swap(branch, &mut right);
        core::mem::swap(&mut branch.parent, &mut right.parent);

        branch.left = Some(right);
    }

    /// TODO
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    fn rotate_right(branch: &mut Box<Node<T>>) {
        let Some(mut left) = branch.left.take() else {
            panic!(); // TODO: handle this more gracefully?
        };

        if let Some(mut left_right) = left.right.take() {
            left_right.parent = Some(core::ptr::NonNull::from(branch.as_mut()));
            branch.left = Some(left_right);
        }

        core::mem::swap(branch, &mut left);
        core::mem::swap(&mut branch.parent, &mut left.parent);

        branch.right = Some(left);
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

    mod node {
        use super::*;

        mod method {
            use super::*;

            mod rotate_left {
                use super::*;
            }

            mod rotate_right {
                use super::*;
            }
        }
    }

    mod method {
        use super::*;

        mod insert {
            use super::*;

            #[test]
            fn adds_element() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                assert!(instance.insert(12345).is_ok());

                assert!(instance.root.is_some());
            }

            #[test]
            fn initializes_element() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                let expected = 12345;

                assert!(instance.insert(expected).is_ok());

                assert!(instance.root.is_some_and(|node| node.element == expected));
            }

            #[test]
            fn into_left_branch_when_less() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                // Insert the root node.
                assert!(instance.insert(0).is_ok());

                // Insert the child node that is less than root.
                let expected = -1;
                assert!(instance.insert(expected).is_ok());

                assert!(instance.root.is_some_and(|root| root.left.is_some_and(|left| left.element == expected)));
            }

            #[test]
            fn into_right_branch_when_greater() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                // Insert the root node.
                assert!(instance.insert(0).is_ok());

                // Insert the child node that is greater than root.
                let expected = 1;
                assert!(instance.insert(expected).is_ok());

                assert!(instance.root.is_some_and(|root| root.right.is_some_and(|right| right.element == expected)));
            }

            #[test]
            fn parent_is_none_when_root() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                assert!(instance.insert(12345).is_ok());

                assert!(instance.root.is_some_and(|root| root.parent.is_none()));
            }

            #[test]
            fn parent_is_some_when_child() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                // Insert root.
                assert!(instance.insert(0).is_ok());

                // Insert left child.
                assert!(instance.insert(-1).is_ok());

                // Insert right child.
                assert!(instance.insert(1).is_ok());

                let ptr = core::ptr::NonNull::from(instance.root.as_deref().unwrap());

                assert!(instance.root.as_ref().is_some_and(|root| root.left.as_ref().is_some_and(|left| left.parent.is_some_and(|parent| parent == ptr))));
                assert!(instance.root.as_ref().is_some_and(|root| root.right.as_ref().is_some_and(|right| right.parent.is_some_and(|parent| parent == ptr))));
            }

            #[test]
            fn errors_when_equivalent_element_is_already_contained() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                assert!(instance.insert(12345).is_ok());

                assert!(instance.insert(12345).is_err());
            }

            #[test]
            fn error_yields_new_element() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                assert!(instance.insert(12345).is_ok());

                assert!(instance.insert(12345).is_err_and(|error| error.0 == 12345));
            }

            #[test]
            fn error_yields_existing_equivalent_element() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                assert!(instance.insert(12345).is_ok());

                assert!(instance.insert(12345).is_err_and(|error| error.1 == &mut 12345));
            }

            mod left_rotate {
                use super::*;

            }

            mod right_rotate {
                use super::*;

            }

            mod left_right_rotate {
                use super::*;

            }

            mod right_left_rotate {
                use super::*;

            }
        }
    }
}
