//! Implementations of [`Graph`].

pub mod rooted_tree;
pub use rooted_tree::RootedTree;

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

/// An instance of an element within a [`Graph`].
pub trait Node {
    /// The type of [`Edge`] which connects [`Self`].
    type Edge<'a>: Edge<'a> where Self: 'a;

    /// Obtain all [`Edge`] connected to `self`.
    #[must_use]
    fn edges(&self) -> impl Iterator<Item = &Self::Edge<'_>>;
}

/// An association between two [`Node`] within a [`Graph`]
pub trait Edge<'a> {
    /// The type this connects.
    type Node: Node;

    /// Obtain the [`Node`] that self associates.
    #[must_use]
    fn nodes(&self) -> (&Self::Node, &Self::Node);
}
