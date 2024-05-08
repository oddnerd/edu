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

    pub fn remove_front(&mut self) -> Option<T> {
        match core::mem::replace(&mut self.head, Link::Empty) {
            Link::Empty => None,
            Link::More(node) => {
                self.head = node.next;
                Some(node.element)
            }
        }
    }
}

impl<T> Default for Singly<T> {
    fn default() -> Self {
        Singly { head: Link::Empty }
    }
}

impl<T> Drop for Singly<T> {
    fn drop(&mut self) {
        let mut current = core::mem::replace(&mut self.head, Link::Empty);

        while let Link::More(mut next) = current {
            current = core::mem::replace(&mut next.next, Link::Empty);
        }
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
