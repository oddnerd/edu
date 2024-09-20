//! Implementation of [`Rooted`].

use super::Tree;

pub trait Rooted : for<'a> Tree<Node: Node, Edge<'a>: Edge<'a>> {
    #[must_use]
    fn root(&self) -> &Self::Node;

    #[must_use]
    fn degree(&self) -> usize;
}

pub trait Node : super::super::Node {
    #[must_use]
    fn parent(&self) -> &Self;

    #[must_use]
    fn children(&self) -> impl Iterator<Item = &Self>;

    #[must_use]
    fn siblings(&self) -> impl Iterator<Item = &Self>;

    #[must_use]
    fn ancestors(&self) -> impl Iterator<Item = &Self>;

    #[must_use]
    fn descendants(&self) -> impl Iterator<Item = &Self>;

    #[must_use]
    fn degree(&self) -> usize {
        self.children().count()
    }

    #[must_use]
    fn level(&self) -> usize;
}
pub trait Edge<'a> : super::super::Edge<'a> {
    #[must_use]
    fn parent(&self) -> &Self::Node;

    #[must_use]
    fn child(&self) -> &Self::Node;
}
