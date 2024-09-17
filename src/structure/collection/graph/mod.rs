//! Implementations of [`Graph`].

use super::Collection;

pub trait Node {
    type Edge: Edge;
}

pub trait Edge {
    type Node: Node;
}

pub trait Graph : Collection {
    type Node: Node<Edge = Self::Edge>;

    type Edge: Edge<Node = Self::Node>;
}
