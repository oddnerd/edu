//! Implementation of [`Singly`].

pub struct Singly<T> {
    head: Option<Box<Node<T>>>,
}

impl<T> Singly<T> {
    pub fn prepend(&mut self, value: T) {
        let new = Box::new(Node {
            element: value,
            next: core::mem::replace(&mut self.head, None),
        });

        self.head = Some(new);
    }

    pub fn remove_front(&mut self) -> Option<T> {
        match core::mem::replace(&mut self.head, None) {
            None => None,
            Some(node) => {
                self.head = node.next;
                Some(node.element)
            }
        }
    }
}

impl<T> Default for Singly<T> {
    fn default() -> Self {
        Singly { head: None }
    }
}

impl<T> Drop for Singly<T> {
    fn drop(&mut self) {
        let mut current = core::mem::replace(&mut self.head, None);

        while let Some(mut next) = current {
            current = core::mem::replace(&mut next.next, None);
        }
    }
}

struct Node<T> {
    element: T,
    next: Option<Box<Node<T>>>
}
