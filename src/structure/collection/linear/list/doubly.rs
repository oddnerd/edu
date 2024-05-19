//! Implementation of [`Doubly`].

use core::ptr::NonNull;

pub struct Doubly<T> {
    /// The node considered to be the first, if any are contained.
    elements: Option<NonNull<Node<T>>>,
}

struct Node<T> {
    /// Ownership of the underlying element.
    element: T,

    /// The node before self, if any.
    predecessor: Option<NonNull<Node<T>>>,

    /// The node after self, if any.
    successor: Option<NonNull<Node<T>>>,
}
