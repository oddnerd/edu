//! Implementation of [`Singly`].

pub struct Singly<T> {
    head: Link<T>,
}

enum Link<T> {
    Empty,
    More(Box<Node<T>>),
}

struct Node<T> {
    element: T,
    next: Link<T>
}
