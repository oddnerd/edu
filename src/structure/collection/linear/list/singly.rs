//! Implementation of [`Singly`].

use super::Collection;
use super::Linear;

/// Independently allocated elements connected via a single link.
///
/// Each element exists within separate allocated object, referred to as a
/// node. Each node contains a single pointer which is said to 'link' to
/// subsequent elements in a [`super::Linear`] sequence. Therefore, [`Self`]
/// points to the first node (if any) and each subsequent node points to the
/// next until the last element which points to nothing as visualized below:
///
/// ```text
///         +-------+    +---------+    +---------+           +------+
/// Self -> | first | -> | element | -> | element | -> ... -> | last |
///         +-------+    +---------+    +---------+           +------+
/// ```
///
/// See also: [Wikipedia](https://en.wikipedia.org/wiki/Linked_list)
pub struct Singly<T> {
    /// The contained elements.
    elements: Option<Box<Node<T>>>,
}

/// An independently allocated element contained within some [`Singly`].
struct Node<T> {
    /// The underlying contained value.
    element: T,

    /// Link to the rest of the list.
    next: Option<Box<Node<T>>>,
}

impl<T> Default for Singly<T> {
    /// Create an empty instance of [`Singly`].
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory for the result.
    fn default() -> Self {
        Singly { elements: None }
    }
}

impl<T> Drop for Singly<T> {
    /// Iteratively drop all contained elements.
    ///
    /// The default destructor implementation will _NOT_ be tail recursive,
    /// hence this provided iterative method to prevent stack overflow.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn drop(&mut self) {
        let mut current = self.elements.take();

        while let Some(mut node) = current {
            current = node.next.take();
        }
    }
}

impl<T> Singly<T> {
    pub fn prepend(&mut self, value: T) {
        let new = Box::new(Node {
            element: value,
            next: self.elements.take(),
        });

        self.elements = Some(new);
    }

    pub fn remove_front(&mut self) -> Option<T> {
        self.elements.take().map(|node| {
            self.elements = node.next;

            node.element
        })
    }

    pub fn peek_front(&self) -> Option<&T> {
        self.elements.as_ref().map(|node| &node.element)
    }

    pub fn peek_front_mut(&mut self) -> Option<&mut T> {
        self.elements.as_mut().map(|node| &mut node.element)
    }
}

impl<T> core::ops::Index<usize> for Singly<T> {
    type Output = T;

    /// Obtain an immutable reference to the element at `index`.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn index(&self, index: usize) -> &Self::Output {
        let Some(mut current) = self.elements.as_ref() else {
            panic!("no elements contained");
        };

        for _ in 0..index {
            if let Some(next) = current.next.as_ref() {
                current = next;
            } else {
                panic!("index out of bounds");
            }
        }

        &current.element
    }
}

impl<T> core::ops::IndexMut<usize> for Singly<T> {
    /// Obtain a mutable reference to the element at `index`.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let Some(mut current) = self.elements.as_mut() else {
            panic!("no elements contained");
        };

        for _ in 0..index {
            if let Some(next) = current.next.as_mut() {
                current = next;
            } else {
                panic!("index out of bounds");
            }
        }

        &mut current.element
    }
}

impl<'a, T: 'a> Collection<'a> for Singly<T> {
    type Element = T;

    /// Query how many elements are contained.
    ///
    /// # Panics
    /// Panics if the number of elements contained is more than [`usize::MAX`].
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn count(&self) -> usize {
        let Some(mut current) = self.elements.as_ref() else {
            return 0;
        };

        let mut count: usize = 1;

        while let Some(next) = current.next.as_ref() {
            if let Some(incremented) = count.checked_add(1) {
                count = incremented;
            } else {
                panic!("too many elements for size type");
            }

            current = next;
        }

        count
    }
}

/// Immutable iterator over a [`Singly`].
struct Iter<T> {
    /// The next element to yield, if any.
    next: Option<Node<T>>,
}
