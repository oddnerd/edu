//! Implementation of [`Rooted`].

pub mod adelson_velsky_landis;
pub use adelson_velsky_landis::AdelsonVelsoLandis;

use super::Graph;
use super::Collection;
use super::Directed;

/// A connected, acyclic [`Graph`] with a defined 'root' [`Node`].
///
/// A [`Graph`] is a 'tree' if it is
///
/// - Connected: there exists a chain of [`Edge`] forming a path from any
///   [`Node`] to _all_ other [`Node`].
/// - Acyclic: there exists no cycles such that any two [`Node`] are connected
///   via _exactly_ one path.
///
/// Such a 'tree' is then 'rooted' if one [`Node`] is defined as the 'root' and
/// all [`Edge`] are directed away from it. This implies a hierarchical
/// structure where for any [`Node`] (except the root), there is exactly one
/// [`Node`] which connects towards it called the 'parent', and all other
/// connection are directed away towards [`Node`] referred to as 'children'.
pub trait RootedTree : for<'a> Directed<Node: Node, Edge<'a>: Edge<'a>> {
    /// Obtain the [`Node`] with no parent.
    ///
    /// The only time this returns `None` is when empty.
    #[must_use]
    fn root(&self) -> Option<&Self::Node>;

    /// Query the maximum number of children a [`Node`] can have.
    #[must_use]
    fn degree(&self) -> usize;

    /// Obtain all [`Node`] which have no children.
    #[must_use]
    fn leaves(&self) -> impl Iterator<Item = &Self::Node>;

    /// Query the number of leaves.
    #[must_use]
    fn breadth(&self) -> usize {
        self.leaves().count()
    }

    /// Query the longest path from the root to a leaf.
    ///
    /// The only time this returns `None` is when empty.
    #[must_use]
    fn height(&self) -> Option<usize>;
}

/// An instance of an element within a [`RootedTree`].
pub trait Node : super::directed::Node {
    /// Obtain the [`Node`] which connects towards `self`.
    ///
    /// The only time this returns `None` is when `self` is the root.
    #[must_use]
    fn parent(&self) -> Option<&Self>;

    /// Obtain all [`Node`] which `self` connects towards.
    #[must_use]
    fn children(&self) -> impl Iterator<Item = &Self>;

    /// Obtain all [`Node`] which have the same parent.
    #[must_use]
    fn siblings(&self) -> impl Iterator<Item = &Self>;

    /// Obtain all [`Node`] in the path between `self` and the root.
    #[must_use]
    fn ancestors(&self) -> impl Iterator<Item = &Self>;

    /// Obtain all [`Node`] for which `self` is an ancestor.
    #[must_use]
    fn descendants(&self) -> impl Iterator<Item = &Self>;

    /// Query if `self` has no children.
    #[must_use]
    fn is_leaf(&self) -> bool {
        self.is_external()
    }

    /// Query if `self` has children.
    #[must_use]
    fn is_branch(&self) -> bool {
        self.is_internal()
    }

    /// Query how many [`Node`] are children of self.
    #[must_use]
    fn degree(&self) -> usize {
        self.children().count()
    }

    /// Query how many [`Node`] are in the path between `self` and the root.
    #[must_use]
    fn level(&self) -> usize {
        self.ancestors().count()
    }
}

/// An association between [`Node`] in a [`RootedTree`].
pub trait Edge<'a> : super::directed::Edge<'a> {
    /// Obtain the [`Node`] which is the parent of the other.
    #[must_use]
    fn parent(&self) -> &Self::Node {
        self.from()
    }

    /// Obtain the [`Node`] which is the child of the other.
    #[must_use]
    fn child(&self) -> &Self::Node {
        self.to()
    }
}
