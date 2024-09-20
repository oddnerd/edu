//! Implementation of [`AdelsonVelskyLandis`].

use super::Rooted;
use super::Tree;
use super::Graph;
use super::Collection;

pub struct AdelsonVelskyLandis<T> {
    root: Option<Node<T>>,
}

struct Node<T> {
    data: T,

    height: usize,

    left: Option<Box<Node<T>>>,
    right: Option<Box<Node<T>>>,
}
