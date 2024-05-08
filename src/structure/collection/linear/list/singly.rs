//! Implementation of [`Singly`].

pub struct Singly<T> {
    head: Link<T>,
}

impl<T> Singly<T> {
    pub fn prepend(&mut self, value: T) {
        let new = Box::new(Node {
            element: value,
            next: core::mem::replace(&mut self.head, Link::Empty),
        });

        self.head = Link::More(new);
    }
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
