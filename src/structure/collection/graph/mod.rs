//! Implementations of [`Graph`].

// TODO: This temporarily disables aggressive warnings within the module for
// the sake of prototyping. This should be removed thereafter, thenceforth
// dealing with each warning individually before even considering merging.
#![allow(missing_docs)]

pub mod tree;
pub mod directed;

pub use tree::Tree;
pub use directed::Directed;

use super::Collection;

pub trait Graph : Collection {
    type Node: for<'a> Node<Edge<'a> = Self::Edge<'a>>;

    type Edge<'a>: Edge<'a, Node = Self::Node>;

    fn edges(&self) -> impl Iterator<Item = Self::Edge<'_>>;

    fn nodes(&self) -> impl Iterator<Item = Self::Node>;
}

pub trait Node {
    type Edge<'a>: Edge<'a> where Self: 'a;

    #[must_use]
    fn edges(&self) -> impl Iterator<Item = Self::Edge<'_>>;
}

pub trait Edge<'a> {
    type Node: Node;

    #[must_use]
    fn nodes(&self) -> (&Self::Node, &Self::Node);
}
