//! Implementation of [`Singly`].

use super::Collection;
use super::Linear;
use super::List;

use std::alloc;

pub enum Singly<T> {
    Empty,
    More(Box<Node<T>>),
}

struct Node<T> {
    element: T,

    next: Singly<T>,
}
