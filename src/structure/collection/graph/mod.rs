//! Implementations of [`Graph`].

pub mod tree;
pub use tree::Tree;

pub mod directed;
pub use directed::Directed;

use super::Collection;

/// A [`Collection`] of [`Node`] that are associated with via [`Edge`].
pub trait Graph : Collection {
    /// The type representing an [`Self::Element`].
    type Node: for<'a> Node<Edge<'a> = Self::Edge<'a>>;

    /// The type which associates [`Node`] with one another.
    type Edge<'a>: Edge<'a, Node = Self::Node>;

    /// Obtain all [`Edge`] contained within `self`.
    fn edges(&self) -> impl Iterator<Item = &Self::Edge<'_>>;

    /// Obtain all [`Node`] contained within `self`.
    fn nodes(&self) -> impl Iterator<Item = &Self::Node>;
}

pub trait Node {
    type Edge<'a>: Edge<'a> where Self: 'a;

    #[must_use]
    fn edges(&self) -> impl Iterator<Item = &Self::Edge<'_>>;
}

pub trait Edge<'a> {
    type Node: Node;

    #[must_use]
    fn nodes(&self) -> (&Self::Node, &Self::Node);
}
