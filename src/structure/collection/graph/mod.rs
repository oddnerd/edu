//! Implementations of [`Graph`].

pub mod tree;
pub use tree::Tree;

pub mod directed;
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
