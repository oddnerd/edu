//! Implementations of [`Graph`].

use super::Collection;

pub trait Node {
    type Edge: Edge;

    fn edges(&self) -> impl Iterator<Item = &impl Edge>;

    fn edges_mut(&mut self) -> impl Iterator<Item = &mut impl Edge>;
}

pub trait Edge {
    type Node: Node;

    fn nodes(&self) -> (&impl Node, &impl Node);

    fn nodes_mut(&mut self) -> (&mut impl Node, &mut impl Node);
}

pub trait Graph : Collection {
    type Node: Node<Edge = Self::Edge>;

    type Edge: Edge<Node = Self::Node>;
}
