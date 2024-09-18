//! Implementations of [`Graph`].

pub mod tree;

pub use tree::Tree;

use super::Collection;

/// An element contained within the a [`Graph`].
pub trait Node<T> : core::ops::DerefMut<Target = T> {
    /// The type connecting this [`Node`] to others in a [`Graph`].
    type Edge: Edge<T>;

    /// Immutably query the [`Edge`] associating this [`Node`] with another.
    fn edges<'a>(&'a self) -> impl Iterator<Item = &'a Self::Edge> where Self::Edge: 'a;

    /// Mutably query the [`Edge`] associating this [`Node`] with another.
    fn edges_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut Self::Edge> where Self::Edge: 'a;
}

/// A connection between (exactly two) [`Node`].
pub trait Edge<T> {
    /// The type this [`Edge`] connects together.
    type Node: Node<T>;

    /// Immutably obtain the [`Node`] connected via this [`Edge`].
    fn nodes(&self) -> (&Self::Node, &Self::Node);

    /// Mutably obtain the [`Node`] connected via this [`Edge`].
    fn nodes_mut(&mut self) -> (&mut Self::Node, &mut Self::Node);
}

/// Complex associations ([`Edge`]) between elements ([`Node`]).
pub trait Graph : Collection {
    /// The type storing an element.
    type Node: Node<Self::Element, Edge = Self::Edge>;

    /// The type associating elements.
    type Edge: Edge<Self::Element, Node = Self::Node>;

    /// Immutable obtain all [`Node`] contained within this [`Graph`].
    fn nodes<'a>(&'a self) -> impl Iterator<Item = &'a Self::Node> where Self::Node: 'a;

    /// Mutably obtain all [`Node`] contained within this [`Graph`].
    fn nodes_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut Self::Node> where Self::Node: 'a;

    /// Immutable obtain all [`Edge`] contained within this [`Graph`].
    fn edges<'a>(&'a self) -> impl Iterator<Item = &'a Self::Edge> where Self::Edge: 'a;

    /// Mutably obtain all [`Edge`] contained within this [`Graph`].
    fn edges_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut Self::Edge> where Self::Edge: 'a;
}
