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
        let mut current = &mut self.root;

        while let &mut Some(ref mut parent) = current {
            current = match element.cmp(&parent.element) {
                core::cmp::Ordering::Less => &mut parent.left,
                core::cmp::Ordering::Greater => &mut parent.right,
                core::cmp::Ordering::Equal => return Err((element, &mut parent.element)),
            };
        }

        let node = Box::new(Node {
            element,
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
            fn inserts_root_node_when_empty() {
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
            fn left_child_when_less_than_root() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                // Insert the root node.
                assert!(instance.insert(0).is_ok());

                // Insert the child node that is less than root.
                let expected = -1;
                assert!(instance.insert(expected).is_ok());

                assert!(instance.root.is_some_and(|root| root.left.is_some_and(|left| left.element == expected)));
            }

            #[test]
            fn right_child_when_greater_than_root() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                // Insert the root node.
                assert!(instance.insert(0).is_ok());

                // Insert the child node that is greater than root.
                let expected = 1;
                assert!(instance.insert(expected).is_ok());

                assert!(instance.root.is_some_and(|root| root.right.is_some_and(|right| right.element == expected)));
            }
        }
    }
}
