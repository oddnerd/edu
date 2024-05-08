//! Implementation of [`Singly`].

pub struct Singly<T> {
    head: Link<T>,
}

impl<T> Default for Singly<T> {
    fn default() -> Self {
        Singly { head: Link::Empty }
    }
}

enum Link<T> {
    Empty,
    More(Box<Node<T>>),
}

struct Node<T> {
    element: T,
    next: Link<T>
}
