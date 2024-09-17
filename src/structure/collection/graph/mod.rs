//! Implementations of [`Graph`].

use super::Collection;

/// An element contained within the a [`Graph`].
pub trait Node {
    /// The type connecting this [`Node`] to others in a [`Graph`].
    type Edge: Edge;

    /// Immutably query the [`Edge`] associating this [`Node`] with another.
    fn edges(&self) -> impl Iterator<Item = &impl Edge>;

    /// Mutably query the [`Edge`] associating this [`Node`] with another.
    fn edges_mut(&mut self) -> impl Iterator<Item = &mut impl Edge>;
}

/// A connection between (exactly two) [`Node`].
pub trait Edge {
    /// The type this [`Edge`] connects together.
    type Node: Node;

    /// Immutably obtain the [`Node`] connected via this [`Edge`].
    fn nodes(&self) -> (&impl Node, &impl Node);

    /// Mutably obtain the [`Node`] connected via this [`Edge`].
    fn nodes_mut(&mut self) -> (&mut impl Node, &mut impl Node);
}

/// Complex associations ([`Edge`]) between elements ([`Node`]).
pub trait Graph : Collection {
    /// The type storing an element.
    type Node: Node<Edge = Self::Edge>;

    /// The type associating elements.
    type Edge: Edge<Node = Self::Node>;

    /// Immutable obtain all [`Node`] contained within this [`Graph`].
    fn nodes(&self) -> impl Iterator<Item = &impl Node>;

    /// Mutably obtain all [`Node`] contained within this [`Graph`].
    fn nodes_mut(&mut self) -> impl Iterator<Item = &mut impl Node>;

    /// Immutable obtain all [`Edge`] contained within this [`Graph`].
    fn edges(&self) -> impl Iterator<Item = &impl Edge>;

    /// Mutably obtain all [`Edge`] contained within this [`Graph`].
    fn edges_mut(&mut self) -> impl Iterator<Item = &mut impl Edge>;
}
