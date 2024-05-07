//! Implementation of [`Singly`].

use super::Collection;
use super::Linear;
use super::List;

use std::alloc;

/// Independently allocated elements connected via a single link.
///
/// Each element exists with a 'node', each of which are a separate allocated
/// object. These nodes are logically arranged in [`super::Linear`] fashion
/// where each element links to the element after it and nothing else.
///
/// See also: [Wikipedia](https://en.wikipedia.org/wiki/Linked_list).
pub struct Singly<T> {
    /// The contained element for this node.
    element: T,

    /// The next element, if there is one.
    next: Option<Box<Singly<T>>>,
}

impl<'a, T: 'a> core::ops::Index<usize> for Singly<T> {
    type Output = T;

    /// Query the element `index` positions from the start.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    fn index(&self, index: usize) -> &Self::Output {
        let mut current = self;

        for _ in 0..index {
            if let Some(next) = &current.next {
                current = next;
            } else {
                panic!("index out of bounds");
            }
        }

        &current.element
    }
}

impl<'a, T: 'a> core::ops::IndexMut<usize> for Singly<T> {
    /// Query the element `index` positions from the start.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// todo!()
    /// ```
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let mut current = self;

        for _ in 0..index {
            if let Some(next) = &mut current.next {
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

    /// Query how many elements are contained in the [`Collection`].
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Panics
    /// Panics if more than [`usize::MAX`] elements are contained.
    ///
    /// # Examples
    /// ```
    /// todo!();
    /// ```
    fn count(&self) -> usize {
        let mut current = self;
        let mut count: usize = 1;

        while let Some(next) = &current.next {
            current = next;

            if let Some(incremented) = count.checked_add(1) {
                count = incremented;
            } else {
                panic!("too many elements to count");
            }
        }

        count
    }
}

/// Immutable [`Iterator`] over the elements within a [`Singly`].
struct Iter<'a, T> {
    /// The next (front) node to yield, if any.
    next: Option<&'a Singly<T>>,

    /// The previously yielded back node, if any.
    previous_back: Option<&'a Singly<T>>,
}

impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;

    /// Obtain the next element from the front.
    ///
    /// # Performance
    /// This method take O(1) time and consumes O(1) memory.
    fn next(&mut self) -> Option<Self::Item> {
        self.next.map(|current| {
            self.next = current.next.as_ref().map(core::convert::AsRef::as_ref);

            if let (Some(next), Some(back)) = (self.next, self.previous_back) {
                if core::ptr::addr_eq(next, back) {
                    self.next = None;
                }
            }

            &current.element
        })
    }

    /// Query how many elements have yet to be yielded.
    ///
    /// # Panics
    /// This method panics if more than [`usize::MAX`] elements.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len(), Some(self.len()))
    }
}

impl<'a, T: 'a> core::iter::FusedIterator for Iter<'a, T> {}

impl<'a, T: 'a> ExactSizeIterator for Iter<'a, T> {
    /// Query how many elements have yet to be yielded.
    ///
    /// # Panics
    /// This method panics if more than [`usize::MAX`] elements.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn len(&self) -> usize {
        let Some(mut current) = self.next else {
            return 0;
        };

        let mut count: usize = 1;

        while let Some(next) = current.next.as_ref() {
            if let Some(back) = self.previous_back {
                if core::ptr::addr_eq(next, back) {
                    break;
                }
            }

            current = next;

            if let Some(incremented) = count.checked_add(1) {
                count = incremented;
            } else {
                panic!("too many elements to count");
            }
        }

        count
    }
}

impl<'a, T: 'a> DoubleEndedIterator for Iter<'a, T> {
    /// Obtain the next element from the back.
    ///
    /// # Performance
    /// This method take O(N) time and consumes O(1) memory.
    fn next_back(&mut self) -> Option<Self::Item> {
        let mut current = self.next?;

        while let Some(next) = current.next.as_ref() {
            if let Some(back) = self.previous_back {
                if core::ptr::addr_eq(next, back) {
                    break;
                }
            }

            current = next;
        }

        self.previous_back = Some(current);

        Some(&current.element)
    }
}
