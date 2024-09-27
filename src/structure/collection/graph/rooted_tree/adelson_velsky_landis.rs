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
        let (mut parent, mut previous) = {
            let mut parent = None;
            let mut branch = &mut self.root;

            while let &mut Some(ref mut node) = branch {
                parent = Some(core::ptr::NonNull::from(node.as_ref()));

                branch = match element.cmp(&node.element) {
                    core::cmp::Ordering::Less => &mut node.left,
                    core::cmp::Ordering::Greater => &mut node.right,
                    core::cmp::Ordering::Equal => return Err((element, &mut node.element)),
                };
            }

            let child = branch.insert(Box::new(Node {
                element,
                parent,
                highest_branch: BalanceFactor::Balanced,
                left: None,
                right: None,
            }));

            (parent, core::ptr::NonNull::from(child.as_ref()))
        };

        while let Some(mut current) = parent {
            // SAFETY: no other references to this node exist.
            let current = unsafe { current.as_mut() };

            if current.left.as_deref().is_some_and(|left| core::ptr::from_ref(left) == previous.as_ptr()) {
                // Ascended via the left branch.

                if current.highest_branch == BalanceFactor::Left {
                    // Insertion made left branch unbalanced.

                    let Some(left) = current.left.as_deref_mut() else {
                        unreachable!("we ascended via the left branch");
                    };

                    if left.highest_branch == BalanceFactor::Right {
                        // rotate_left(current.left)
                    }

                    // rotate_right(current);
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

                    let Some(right) = current.right.as_deref_mut() else {
                        unreachable!("we ascended via the right branch");
                    };

                    if right.highest_branch == BalanceFactor::Left {
                        // rotate_right(current.right)
                    }

                    // rotate_left(current);
                } else if current.highest_branch == BalanceFactor::Left {
                    // Insertion balanced this left-heavy node.

                    current.highest_branch = BalanceFactor::Balanced;
                    break;
                } else {
                    // No imbalance yet, propagate balance factor up ancestors.
                    current.highest_branch = BalanceFactor::Right;
                }
            }

            parent = current.parent;
            previous = core::ptr::NonNull::from(current);
        }

        todo!()
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
    parent: Option<core::ptr::NonNull<Node<T>>>,

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
    fn rotate_left(mut root: Box<Self>) -> Box<Self> {
        let Some(mut right) = root.right.take() else {
            panic!()
        };

        if let Some(mut right_left) = right.left.take() {
            right_left.parent = Some(core::ptr::NonNull::from(root.as_ref()));
            root.right = Some(right_left);
        }

        core::mem::swap(&mut right.parent, &mut root.parent);

        right.left = Some(root);

        right
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
    fn rotate_right(mut root: Box<Self>) -> Box<Self> {
        let Some(mut left) = root.left.take() else {
            panic!()
        };

        if let Some(mut left_right) = left.right.take() {
            left_right.parent = Some(core::ptr::NonNull::from(root.as_ref()));
            root.left = Some(left_right);
        }

        core::mem::swap(&mut left.parent, &mut root.parent);

        left.right = Some(root);

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

    mod node {
        use super::*;

        mod method {
            use super::*;

            mod rotate_left {
                use super::*;

                /// Construct a standard tree and perform a left rotation.
                ///
                /// First constructs the following tree:
                ///
                /// ```DOT
                /// digraph {
                ///     "root" -> "left-child"
                ///     "root" -> "right-child"
                ///
                ///     "right-child" -> "left-grandchild"
                ///     "right-child" -> "right-grandchild"
                /// }
                ///```
                ///
                /// then calls [`Node::rotate_left`] which _should_ produce
                ///
                ///```dot
                /// digraph {
                ///     "right-child" -> "root"
                ///     "right-child" -> "right-grandchild"
                ///
                ///     "root" -> "left-child"
                ///     "root" -> "left-grandchild"
                /// }
                /// ```
                fn new<'a>() -> Box<Node<&'a str>> {
                    let mut root = Box::new(Node {
                        element: "root",
                        highest_branch: BalanceFactor::Right,
                        parent: None,
                        left: None,
                        right: None,
                    });

                    root.left = Some(Box::new(Node {
                        element: "left-child",
                        highest_branch: BalanceFactor::Balanced,
                        parent: Some(core::ptr::NonNull::from(root.as_ref())),
                        left: None,
                        right: None,
                    }));

                    let right = root.right.insert(Box::new(Node {
                        element: "right-child",
                        highest_branch: BalanceFactor::Balanced,
                        parent: Some(core::ptr::NonNull::from(root.as_ref())),
                        left: None,
                        right: None,
                    }));

                    right.left = Some(Box::new(Node {
                        element: "left-grandchild",
                        highest_branch: BalanceFactor::Balanced,
                        parent: Some(core::ptr::NonNull::from(right.as_ref())),
                        left: None,
                        right: None,
                    }));

                    right.right = Some(Box::new(Node {
                        element: "right-grandchild",
                        highest_branch: BalanceFactor::Balanced,
                        parent: Some(core::ptr::NonNull::from(right.as_ref())),
                        left: None,
                        right: None,
                    }));

                    Node::rotate_left(root)
                }

                #[test]
                fn elements_are_reordered() {
                    let root = new();
                    assert_eq!(root.element, "right-child");

                    let right = root.right.unwrap();
                    assert_eq!(right.element, "right-grandchild");

                    let left = root.left.unwrap();
                    assert_eq!(left.element, "root");

                    let left_left = left.left.unwrap();
                    assert_eq!(left_left.element, "left-child");

                    let left_right = left.right.unwrap();
                    assert_eq!(left_right.element, "left-grandchild");
                }

                #[test]
                fn parents_are_updated() {
                    let root = new();
                    assert!(root.parent.is_none());

                    let right = root.right.as_ref().unwrap();
                    assert_eq!(right.parent, Some(core::ptr::NonNull::from(root.as_ref())));

                    let left = root.left.as_ref().unwrap();
                    assert_eq!(left.parent, Some(core::ptr::NonNull::from(root.as_ref())));

                    let left_left = left.left.as_ref().unwrap();
                    assert_eq!(left_left.parent, Some(core::ptr::NonNull::from(left.as_ref())));

                    let left_right = left.right.as_ref().unwrap();
                    assert_eq!(left_right.parent, Some(core::ptr::NonNull::from(left.as_ref())));
                }
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
            fn yields_element() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                let mut expected = 12345;

                assert!(instance.insert(expected).is_ok_and(|actual| actual == &mut expected));
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

            mod errors {
                use super::*;

                #[test]
                fn when_equivalent_element_already_contained() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    assert!(instance.insert(12345).is_ok());

                    assert!(instance.insert(12345).is_err());
                }

                #[test]
                fn yields_new_element() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    assert!(instance.insert(12345).is_ok());

                    assert!(instance.insert(12345).is_err_and(|error| error.0 == 12345));
                }

                #[test]
                fn yields_existing_equivalent_element() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    assert!(instance.insert(12345).is_ok());

                    assert!(instance.insert(12345).is_err_and(|error| error.1 == &mut 12345));
                }
            }

            mod balance_factor {
                use super::*;

                #[test]
                fn inserted_node_is_balanced() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    assert!(instance.insert(0).is_ok());

                    assert!(instance.root.is_some_and(|node| node.highest_branch == BalanceFactor::Balanced));
                }

                #[test]
                fn left_balanced_when_left_branch() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    // Insert the root.
                    assert!(instance.insert(0).is_ok());

                    // Insert a left child.
                    assert!(instance.insert(-1).is_ok());

                    assert!(instance.root.is_some_and(|node| node.highest_branch == BalanceFactor::Left));
                }

                #[test]
                fn right_balanced_when_right_branch() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    // Insert the root.
                    assert!(instance.insert(0).is_ok());

                    // Insert a right child.
                    assert!(instance.insert(1).is_ok());

                    assert!(instance.root.is_some_and(|node| node.highest_branch == BalanceFactor::Right));
                }

                #[test]
                fn balanced_when_left_branch_and_then_right_branch() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    // Insert the root.
                    assert!(instance.insert(0).is_ok());

                    // Insert a right child.
                    assert!(instance.insert(1).is_ok());

                    // Insert a left child.
                    assert!(instance.insert(-1).is_ok());

                    assert!(instance.root.is_some_and(|node| node.highest_branch == BalanceFactor::Balanced));
                }

                #[test]
                fn balanced_when_right_branch_and_then_left_branch() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    // Insert the root.
                    assert!(instance.insert(0).is_ok());

                    // Insert a left child.
                    assert!(instance.insert(-1).is_ok());

                    // Insert a right child.
                    assert!(instance.insert(1).is_ok());

                    assert!(instance.root.is_some_and(|node| node.highest_branch == BalanceFactor::Balanced));
                }
            }

            mod left_rotate {
                use super::*;

                /// Insert elements to induce a left rotation.
                ///
                /// This is a helper function which normalizes the [`Node`]
                /// tested within this module.
                ///
                /// The insertions create the following structure
                ///
                ///  0
                /// / \
                ///   1
                ///  / \
                ///    2
                ///
                /// which should be rebalanced via a left-rotation into below
                ///
                ///   1
                ///  / \
                ///  0 2
                fn insert_elements(instance: &mut AdelsonVelsoLandis<i32>) {
                    // Insert the root.
                    assert!(instance.insert(0).is_ok());

                    // Insert a right child.
                    assert!(instance.insert(1).is_ok());

                    // Insert a right grandchild.
                    assert!(instance.insert(2).is_ok());
                }

                #[test]
                fn rotates_elements() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    insert_elements(&mut instance);

                    assert!(instance.root.as_ref().is_some_and(|root| root.element == 1));
                    assert!(instance.root.as_ref().is_some_and(|root| root.left.as_ref().is_some_and(|left| left.element == 0)));
                    assert!(instance.root.as_ref().is_some_and(|root| root.right.as_ref().is_some_and(|right| right.element == 2)));
                }

                #[test]
                fn updates_parents() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    insert_elements(&mut instance);

                    assert!(instance.root.as_ref().is_some_and(|root| root.parent.is_none()));

                    let ptr = core::ptr::NonNull::from(instance.root.as_deref().unwrap());

                    assert!(instance.root.as_deref().is_some_and(|root| root.left.as_deref().is_some_and(|left| left.parent.is_some_and(|parent| parent == ptr))));
                    assert!(instance.root.as_deref().is_some_and(|root| root.right.as_deref().is_some_and(|right| right.parent.is_some_and(|parent| parent == ptr))));
                }
            }

            mod right_rotate {
                use super::*;

                /// Insert elements to induce a right rotation.
                ///
                /// This is a helper function which normalizes the [`Node`]
                /// tested within this module.
                ///
                /// The insertions create the following structure
                ///
                ///     0
                ///    / \
                ///   -1
                ///   / \
                ///  -2
                ///
                /// which should be rebalanced via a left-rotation into below
                ///
                ///   -1
                ///  / \
                /// -2 0
                fn insert_elements(instance: &mut AdelsonVelsoLandis<i32>) {
                    // Insert the root.
                    assert!(instance.insert(0).is_ok());

                    // Insert a left child.
                    assert!(instance.insert(-1).is_ok());

                    // Insert a left grandchild.
                    assert!(instance.insert(-2).is_ok());
                }

                #[test]
                fn rotates_elements() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    insert_elements(&mut instance);

                    assert!(instance.root.as_ref().is_some_and(|root| root.element == -1));
                    assert!(instance.root.as_ref().is_some_and(|root| root.left.as_ref().is_some_and(|left| left.element == -1)));
                    assert!(instance.root.as_ref().is_some_and(|root| root.right.as_ref().is_some_and(|right| right.element == 0)));
                }

                #[test]
                fn updates_parents() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    insert_elements(&mut instance);

                    assert!(instance.root.as_ref().is_some_and(|root| root.parent.is_none()));

                    let ptr = core::ptr::NonNull::from(instance.root.as_deref().unwrap());

                    assert!(instance.root.as_deref().is_some_and(|root| root.left.as_deref().is_some_and(|left| left.parent.is_some_and(|parent| parent == ptr))));
                    assert!(instance.root.as_deref().is_some_and(|root| root.right.as_deref().is_some_and(|right| right.parent.is_some_and(|parent| parent == ptr))));
                }
            }

            mod left_right_rotate {
                use super::*;

                /// Insert elements to induce a left-right rotation.
                ///
                /// This is a helper function which normalizes the [`Node`]
                /// tested within this module.
                ///
                /// The insertions create the following structure
                ///
                ///     3
                ///    / \
                ///    1
                ///   / \
                ///     2
                ///
                /// which should be rebalanced via a left-right-rotation into below
                ///
                ///   2
                ///  / \
                ///  1 3
                fn insert_elements(instance: &mut AdelsonVelsoLandis<i32>) {
                    // Insert the root.
                    assert!(instance.insert(3).is_ok());

                    // Insert a left child.
                    assert!(instance.insert(1).is_ok());

                    // Insert a right grandchild.
                    assert!(instance.insert(2).is_ok());
                }

                #[test]
                fn rotates_elements() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    insert_elements(&mut instance);

                    assert!(instance.root.as_ref().is_some_and(|root| root.element == 2));
                    assert!(instance.root.as_ref().is_some_and(|root| root.left.as_ref().is_some_and(|left| left.element == 1)));
                    assert!(instance.root.as_ref().is_some_and(|root| root.right.as_ref().is_some_and(|right| right.element == 3)));
                }

                #[test]
                fn updates_parents() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    insert_elements(&mut instance);

                    assert!(instance.root.as_ref().is_some_and(|root| root.parent.is_none()));

                    let ptr = core::ptr::NonNull::from(instance.root.as_deref().unwrap());

                    assert!(instance.root.as_deref().is_some_and(|root| root.left.as_deref().is_some_and(|left| left.parent.is_some_and(|parent| parent == ptr))));
                    assert!(instance.root.as_deref().is_some_and(|root| root.right.as_deref().is_some_and(|right| right.parent.is_some_and(|parent| parent == ptr))));
                }
            }

            mod right_left_rotate {
                use super::*;

                /// Insert elements to induce a right-left rotation.
                ///
                /// This is a helper function which normalizes the [`Node`]
                /// tested within this module.
                ///
                /// The insertions create the following structure
                ///
                ///     2
                ///    / \
                ///      1
                ///     / \
                ///     0
                ///
                /// which should be rebalanced via a right-left-rotation into below
                ///
                ///   0
                ///  / \
                ///  1 2
                fn insert_elements(instance: &mut AdelsonVelsoLandis<i32>) {
                    // Insert the root.
                    assert!(instance.insert(2).is_ok());

                    // Insert a right child.
                    assert!(instance.insert(1).is_ok());

                    // Insert a left grandchild.
                    assert!(instance.insert(0).is_ok());
                }

                #[test]
                fn rotates_elements() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    insert_elements(&mut instance);

                    assert!(instance.root.as_ref().is_some_and(|root| root.element == 0));
                    assert!(instance.root.as_ref().is_some_and(|root| root.left.as_ref().is_some_and(|left| left.element == 1)));
                    assert!(instance.root.as_ref().is_some_and(|root| root.right.as_ref().is_some_and(|right| right.element == 2)));
                }

                #[test]
                fn updates_parents() {
                    let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                    insert_elements(&mut instance);

                    assert!(instance.root.as_ref().is_some_and(|root| root.parent.is_none()));

                    let ptr = core::ptr::NonNull::from(instance.root.as_deref().unwrap());

                    assert!(instance.root.as_deref().is_some_and(|root| root.left.as_deref().is_some_and(|left| left.parent.is_some_and(|parent| parent == ptr))));
                    assert!(instance.root.as_deref().is_some_and(|root| root.right.as_deref().is_some_and(|right| right.parent.is_some_and(|parent| parent == ptr))));
                }
            }
        }
    }
}
