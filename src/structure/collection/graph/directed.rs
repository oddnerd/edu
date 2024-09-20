//! Implementations of [`Directed`].

use super::Graph;

pub trait Directed : for<'a> Graph<Edge<'a>: Edge<'a>> {}

pub trait Edge<'a> : super::Edge<'a> {
    fn from(&self) -> &Self::Node;

    fn to(&self) -> &Self::Node;
}
