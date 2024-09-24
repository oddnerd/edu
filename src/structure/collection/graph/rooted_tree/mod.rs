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
/// structure where for any [`Node`], there is exactly one [`Node`] which
/// connects towards it called the 'parent', and all other connection are
/// directed away towards [`Node`] referred to as 'children'.
pub trait RootedTree : for<'a> Directed<Node: Node, Edge<'a>: Edge<'a>> {
    #[must_use]
    fn root(&self) -> &Self::Node;

    #[must_use]
    fn degree(&self) -> usize;

    #[must_use]
    fn leaves(&self) -> impl Iterator<Item = &Self::Node>;

    #[must_use]
    fn breadth(&self) -> usize {
        self.leaves().count()
    }

    #[must_use]
    fn height(&self) -> usize;
}

pub trait Node : super::Node {
    #[must_use]
    fn is_leaf(&self) -> bool;

    #[must_use]
    fn is_branch(&self) -> bool;

    #[must_use]
    fn parent(&self) -> &Self;

    #[must_use]
    fn children(&self) -> impl Iterator<Item = &Self>;

    #[must_use]
    fn siblings(&self) -> impl Iterator<Item = &Self>;

    #[must_use]
    fn ancestors(&self) -> impl Iterator<Item = &Self>;

    #[must_use]
    fn descendants(&self) -> impl Iterator<Item = &Self>;

    #[must_use]
    fn degree(&self) -> usize {
        self.children().count()
    }

    #[must_use]
    fn level(&self) -> usize;
}
pub trait Edge<'a> : super::Edge<'a> {
    #[must_use]
    fn parent(&self) -> &Self::Node;

    #[must_use]
    fn child(&self) -> &Self::Node;
}
