//! Implementation of [`Directed`].

use super::Graph;

pub trait Directed : for<'a> Graph<Edge<'a>: Edge<'a>, Node: Node> {}

pub trait Node : super::Node {
    #[must_use]
    fn is_internal(&self) -> bool;

    #[must_use]
    fn is_external(&self) -> bool;

    #[must_use]
    fn in_degree(&self) -> usize;

    #[must_use]
    fn out_degree(&self) -> usize;
}

pub trait Edge<'a> : super::Edge<'a> {
    #[must_use]
    fn from(&self) -> &Self::Node;

    #[must_use]
    fn to(&self) -> &Self::Node;
}
