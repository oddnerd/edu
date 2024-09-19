//! Implementation of [`AdelsonVelskyLandis`].

use super::Binary;
use super::Tree;
use super::Graph;
use super::Collection;

/// TODO: [Wikipedia](https://en.wikipedia.org/wiki/AVL_tree)
pub struct AdelsonVelskyLandis<T> {
    /// The root node of this tree.
    root: Option<Node<T>>
}

impl<T> Binary for AdelsonVelskyLandis<T> {}

impl<T> Tree for AdelsonVelskyLandis<T> {}

impl<T> Graph for AdelsonVelskyLandis<T> {}

impl<T> Collection for AdelsonVelskyLandis<T> {
    type Element = T;

    /// TODO
    fn count(&self) -> usize {
        todo!()
    }
}

/// An instantiated element with an [`AdelsonVelskyLandis`].
pub struct Node<T> {
    /// The underlying element.
    element: T,

    /// The left child branch, if there is one.
    left: Option<Box<Node<T>>>,

    /// The right child branch, if there is one.
    right: Option<Box<Node<T>>>,
}

/// A link between two [`Node`] in a [`AdelsonVelskyLandis`].
pub struct Edge<'a, T> (&'a Node<T>, &'a Node<T>);
