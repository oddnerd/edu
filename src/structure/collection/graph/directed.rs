//! Implementation of [`Directed`].

use super::Graph;

/// A [`Graph`] whose [`Edge`] has a direction from one [`Node`] to the other.
pub trait Directed : for<'a> Graph<Edge<'a>: Edge<'a>, Node: Node> {}

/// An instance of an element within a [`Directed`] [`Graph`].
pub trait Node : super::Node {
    /// Query if `self` links towards another [`Node`].
    #[must_use]
    fn is_internal(&self) -> bool;

    /// Query if `self` does _not_ link towards another [`Node`].
    #[must_use]
    fn is_external(&self) -> bool;

    /// Query how many [`Node`] connect towards `self`.
    #[must_use]
    fn in_degree(&self) -> usize;

    /// Query how many [`Node`] `self` connects towards.
    #[must_use]
    fn out_degree(&self) -> usize;
}

pub trait Edge<'a> : super::Edge<'a> {
    #[must_use]
    fn from(&self) -> &Self::Node;

    #[must_use]
    fn to(&self) -> &Self::Node;
}
