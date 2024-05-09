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
struct Iter<'a, T> {
    /// The next element to yield, if any.
    next: Option<&'a Node<T>>,

    /// The previously yielded element from the back, if any.
    previous_back: Option<&'a Node<T>>,
}

impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;

    /// Obtain the next element from the front, if any.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().map(|current| {
            self.next = current.next.as_deref();

            if let (Some(next), Some(sentinel)) = (self.next, self.previous_back) {
                if core::ptr::addr_eq(next, sentinel) {
                    self.next = None;
                }
            }

            &current.element
        })
    }

    /// Query how many elements have yet to be yielded.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn size_hint(&self) -> (usize, Option<usize>) {
        let Some(mut current) = self.next else {
            return (0, Some(0));
        };

        let mut count: usize = 1;

        while let Some(next) = current.next.as_deref() {
            if let Some(incremented) = count.checked_add(1) {
                count = incremented;
            } else {
                // Upper bound is larger than can be stored in `usize`.
                return (usize::MAX, None);
            }

            if let Some(sentinel) = self.previous_back {
                if core::ptr::addr_eq(next, sentinel) {
                    break;
                }
            }

            current = next;
        }

        (count, Some(count))
    }
}

impl<'a, T: 'a> DoubleEndedIterator for Iter<'a, T> {
    /// Obtain the next element from the back, if any.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn next_back(&mut self) -> Option<Self::Item> {
        let mut current = self.next?;

        while let Some(next) = current.next.as_deref() {
            if let Some(sentinel) = self.previous_back {
                if core::ptr::addr_eq(next, sentinel) {
                    break;
                }
            }

            current = next;
        }

        self.previous_back = Some(current);

        if let Some(next) = self.next {
            if core::ptr::addr_eq(next, current) {
                self.next = None;
            }
        }

        Some(&current.element)
    }
}

impl<'a, T: 'a> ExactSizeIterator for Iter<'a, T> {}

impl<'a, T: 'a> core::iter::FusedIterator for Iter<'a, T> {}

/// Mutable iterator over a [`Singly`].
struct IterMut<'a, T> {
    /// The next element to yield, if any.
    next: Option<&'a mut Node<T>>,

    /// The previously yielded element from the back, if any.
    previous_back: Option<*const Node<T>>,
}

impl<'a, T: 'a> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    /// Obtain the next element from the front, if any.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().map(|current| {
            self.next = current.next.as_deref_mut();

            if let (Some(next), Some(sentinel)) = (self.next.as_deref(), self.previous_back) {
                if core::ptr::addr_eq(next, sentinel) {
                    self.next = None;
                }
            }

            &mut current.element
        })
    }

    /// Query how many elements have yet to be yielded.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn size_hint(&self) -> (usize, Option<usize>) {
        let Some(mut current) = self.next.as_deref() else {
            return (0, Some(0));
        };

        let mut count: usize = 1;

        while let Some(next) = current.next.as_deref() {
            if let Some(incremented) = count.checked_add(1) {
                count = incremented;
            } else {
                // Upper bound is larger than can be stored in `usize`.
                return (usize::MAX, None);
            }

            if let Some(sentinel) = self.previous_back {
                if core::ptr::addr_eq(next, sentinel) {
                    break;
                }
            }

            current = next;
        }

        (count, Some(count))
    }
}

impl<'a, T: 'a> DoubleEndedIterator for IterMut<'a, T> {
    /// Obtain the next element from the back, if any.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn next_back(&mut self) -> Option<Self::Item> {
        // TODO(oddnerd): this whole method is using pointers to work around reference
        // lifetime restrictions, therefore the validity of yielded references
        // ought to be questioned. Unit testing will hopefully validate the
        // quality of my assumptions?

        let mut current = core::ptr::from_mut(self.next.as_deref_mut()?);

        // SAFETY: the pointer non-null and aligned to an initialized object.
        while let Some(next) = unsafe { &mut *current }.next.as_deref_mut() {
            if let Some(sentinel) = self.previous_back {
                if core::ptr::addr_eq(next, sentinel) {
                    break;
                }
            }

            current = next;
        }

        self.previous_back = Some(current);

        if let Some(next) = self.next.as_deref_mut() {
            if core::ptr::addr_eq(next, current) {
                self.next = None;
            }
        }

        // SAFETY:
        // * we have a unique mutable reference to all elements of `Self`,
        // * this will _NEVER_ yield multiple references to the same element,
        //   (this includes preventing `next` (front) from referencing it)
        // * the yielded references has lifetime of `Self`.
        Some(&mut unsafe { &mut *current }.element)
    }
}

impl<'a, T: 'a> ExactSizeIterator for IterMut<'a, T> {}

impl<'a, T: 'a> core::iter::FusedIterator for IterMut<'a, T> {}
