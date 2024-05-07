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
