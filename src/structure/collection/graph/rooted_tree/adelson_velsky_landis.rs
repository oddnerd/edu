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
    pub fn insert(&mut self, element: T) -> &mut T {
        let mut current = &mut self.root;

        while let &mut Some(ref mut parent) = current {
            current = if element < parent.element {
                &mut parent.left
            } else {
                &mut parent.right
            };
        }

        let node = Box::new(Node {
            element,
            left: None,
            right: None,
        });

        let node = current.insert(node);

        &mut node.element
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

                _ = instance.insert(12345);

                assert!(instance.root.is_some());
                assert_eq!(instance.root.unwrap().element, 12345);
            }

            #[test]
            fn yields_element() {
                let mut instance = AdelsonVelsoLandis::<i32> { root: None };

                let mut expected = 12345;

                let actual = instance.insert(expected);

                assert_eq!(actual, &mut expected);
            }
        }
    }
}
