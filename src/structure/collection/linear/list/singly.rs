//! Implementation of [`Singly`].

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

        while let Some(mut next) = current {
            current = next.next.take();
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
