//! Implementations of [`Graph`].

use super::Collection;

/// An element contained within the a [`Graph`].
pub trait Node {
    /// The type connecting this [`Node`] to others in a [`Graph`].
    type Edge: Edge;

    fn edges(&self) -> impl Iterator<Item = &impl Edge>;

    fn edges_mut(&mut self) -> impl Iterator<Item = &mut impl Edge>;
}

/// A connection between (exactly two) [`Node`].
pub trait Edge {
    /// The type this [`Edge`] connects together.
    type Node: Node;

    fn nodes(&self) -> (&impl Node, &impl Node);

    fn nodes_mut(&mut self) -> (&mut impl Node, &mut impl Node);
}

/// Complex associations ([`Edge`]) between elements ([`Node`]).
pub trait Graph : Collection {
    /// The type storing an element.
    type Node: Node<Edge = Self::Edge>;

    /// The type associating elements.
    type Edge: Edge<Node = Self::Node>;

    fn nodes(&self) -> impl Iterator<Item = &impl Node>;
    fn nodes_mut(&mut self) -> impl Iterator<Item = &mut impl Node>;

    fn edges(&self) -> impl Iterator<Item = &impl Edge>;
    fn edges_mut(&mut self) -> impl Iterator<Item = &mut impl Edge>;
}
