//! Implementation of [`Singly`].

pub struct Singly<T> {
    head: Option<Box<Node<T>>>,
}

impl<T> Singly<T> {
    pub fn prepend(&mut self, value: T) {
        let new = Box::new(Node {
            element: value,
            next: self.head.take(),
        });

        self.head = Some(new);
    }

    pub fn remove_front(&mut self) -> Option<T> {
        self.head.take().map(|node| {
            self.head = node.next;

            node.element
        })
    }

    pub fn peek_front(&self) -> Option<&T> {
        self.head.as_ref().map(|node| {
            &node.element
        })
    }

    pub fn peek_front_mut(&mut self) -> Option<&mut T> {
        self.head.as_mut().map(|node| {
            &mut node.element
        })
    }
}

impl<T> Default for Singly<T> {
    fn default() -> Self {
        Singly { head: None }
    }
}

impl<T> Drop for Singly<T> {
    fn drop(&mut self) {
        let mut current = self.head.take();

        while let Some(mut next) = current {
            current = next.next.take();
        }
    }
}

struct Node<T> {
    element: T,
    next: Option<Box<Node<T>>>
}
