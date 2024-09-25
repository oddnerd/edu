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
    pub fn insert(&mut self, element: T) -> Result<&mut T, (T, &mut T)> {
        let mut parent_ptr = None;

        let mut current = &mut self.root;

        while let &mut Some(ref mut parent) = current {
            parent_ptr = Some(core::ptr::from_mut(parent.as_mut()));

            current = match element.cmp(&parent.element) {
                core::cmp::Ordering::Less => &mut parent.left,
                core::cmp::Ordering::Greater => &mut parent.right,
                core::cmp::Ordering::Equal => return Err((element, &mut parent.element)),
            };
        }

        let node = Box::new(Node {
            element,
            parent: parent_ptr,
            left: None,
            right: None,
        });

        let node = current.insert(node);

        Ok(&mut node.element)
    }
}

/// An instantiated element within a [`AdelsonVelskyLandis`].
struct Node<T> {
    /// The underlying element.
    element: T,

    /// The parent of `self`, if any.
    parent: Option<*mut Node<T>>,

    /// The left child, if any.
    left: Option<Box<Node<T>>>,

    /// The right child, if any.
    right: Option<Box<Node<T>>>,
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
            fn yields_element() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                let mut expected = 12345;

                assert!(instance.insert(expected).is_ok_and(|actual| actual == &mut expected));
            }

            #[test]
            fn left_child_when_less() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                // Insert the root node.
                assert!(instance.insert(0).is_ok());

                // Insert the child node that is less than root.
                let expected = -1;
                assert!(instance.insert(expected).is_ok());

                assert!(instance.root.is_some_and(|root| root.left.is_some_and(|left| left.element == expected)));
            }

            #[test]
            fn right_child_when_greater() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                // Insert the root node.
                assert!(instance.insert(0).is_ok());

                // Insert the child node that is greater than root.
                let expected = 1;
                assert!(instance.insert(expected).is_ok());

                assert!(instance.root.is_some_and(|root| root.right.is_some_and(|right| right.element == expected)));
            }

            #[test]
            fn does_not_set_parent_when_root() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                assert!(instance.insert(12345).is_ok());

                assert!(instance.root.is_some_and(|root| root.parent.is_none()));
            }

            #[test]
            fn sets_parent_when_not_root() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                // Insert root.
                assert!(instance.insert(0).is_ok());

                // Insert child.
                assert!(instance.insert(1).is_ok());

                let ptr = core::ptr::NonNull::from(instance.root.as_mut().unwrap().as_mut());

                assert!(instance.root.is_some_and(|root| root.right.is_some_and(|right| right.parent.is_some_and(|parent| parent == ptr))));
            }

            mod errors {
                use super::*;

                #[test]
                fn errors_when_equivalent_element_already_inserted() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    assert!(instance.insert(12345).is_ok());

                    assert!(instance.insert(12345).is_err());
                }

                #[test]
                fn errors_with_new_element() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    assert!(instance.insert(12345).is_ok());

                    assert!(instance.insert(12345).is_err_and(|error| error.0 == 12345));
                }

                #[test]
                fn error_with_existing_element() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    assert!(instance.insert(12345).is_ok());

                    assert!(instance.insert(12345).is_err_and(|error| error.1 == &mut 12345));
                }
            }

            mod balance_factor {
                use super::*;

                #[test]
                fn new_node_has_balanced_subtrees() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    assert!(instance.insert(0).is_ok());

                    assert!(instance.root.is_some_and(|node| node.balance_factor == BalanceFactor::Balanced));
                }

                #[test]
                fn parent_is_left_balanced_when_inserting_left_child() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    // Insert the root.
                    assert!(instance.insert(0).is_ok());

                    // Insert a left child.
                    assert!(instance.insert(-1).is_ok());

                    assert!(instance.root.is_some_and(|node| node.balance_factor == BalanceFactor::Left));
                }

                #[test]
                fn parent_is_right_balanced_when_inserting_left_child() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    // Insert the root.
                    assert!(instance.insert(0).is_ok());

                    // Insert a right child.
                    assert!(instance.insert(1).is_ok());

                    assert!(instance.root.is_some_and(|node| node.balance_factor == BalanceFactor::Right));
                }

                #[test]
                fn parent_is_balanced_when_inserting_left_after_right() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    // Insert the root.
                    assert!(instance.insert(0).is_ok());

                    // Insert a right child.
                    assert!(instance.insert(1).is_ok());

                    // Insert a left child.
                    assert!(instance.insert(-1).is_ok());

                    assert!(instance.root.is_some_and(|node| node.balance_factor == BalanceFactor::Balanced));
                }

                #[test]
                fn parent_is_balanced_when_inserting_right_after_left() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    // Insert the root.
                    assert!(instance.insert(0).is_ok());

                    // Insert a left child.
                    assert!(instance.insert(-1).is_ok());

                    // Insert a right child.
                    assert!(instance.insert(1).is_ok());

                    assert!(instance.root.is_some_and(|node| node.balance_factor == BalanceFactor::Balanced));
                }
            }

            mod left_rotate {
                use super::*;

                #[test]
                fn does_left_rotation_when_inserting_right_after_right() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    // Insert the root.
                    assert!(instance.insert(0).is_ok());

                    // Insert a right child.
                    assert!(instance.insert(1).is_ok());

                    // Insert a right grandchild.
                    assert!(instance.insert(2).is_ok());

                    // The insertions create the following structure
                    //
                    //  0
                    // / \
                    //   1
                    //  / \
                    //    2
                    //
                    // which should be rebalanced via a left-rotation into below
                    //
                    //   1
                    //  / \
                    //  0 2

                    assert!(instance.root.as_ref().is_some_and(|root| root.element == 1));
                    assert!(instance.root.as_ref().is_some_and(|root| root.left.as_ref().is_some_and(|left| left.element == 0)));
                    assert!(instance.root.as_ref().is_some_and(|root| root.right.as_ref().is_some_and(|right| right.element == 2)));
                }
            }


        }
    }
}
