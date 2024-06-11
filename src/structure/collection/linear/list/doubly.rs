//! Implementation of [`Doubly`].

extern crate alloc;

use core::ptr::NonNull;

use super::super::Stack;
use super::Collection;
use super::Linear;
use super::List;

/// Independently allocated elements connected via two links.
///
/// Each element exists within separate allocated object, referred to as a
/// node. Each node contains a pointer to the previous node alongside a pointer
/// to the subsequent node. [`Self`] maintains independent pointers to both the
/// first and last node thereby allowing constant access to both ends as
/// visualized below:
///
/// ```text
///         +-------+ -> +---------+ -> +---------+ -> ... -> +------+
/// Self -> | first |    | element |    | element |           | last | <- Self
///         +-------+ <- +---------+ <- +---------+ <- ... <- +------+
/// ```
///
/// See also: [Wikipedia](https://en.wikipedia.org/wiki/Linked_list)
pub struct Doubly<T> {
    /// The node considered to be the first/front, if any are contained.
    head: Option<NonNull<Node<T>>>,

    /// The node considered to be the last/back, if any are contained.
    tail: Option<NonNull<Node<T>>>,
}

/// An independently allocated element contained within some [`Doubly`].
struct Node<T> {
    /// Ownership of the underlying element.
    element: T,

    /// The node before self, if any.
    predecessor: Option<NonNull<Node<T>>>,

    /// The node after self, if any.
    successor: Option<NonNull<Node<T>>>,
}

impl<T> Drop for Doubly<T> {
    /// Drop all contained elements.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// drop(instance);
    /// ```
    fn drop(&mut self) {
        self.for_each(drop);
    }
}

impl<T> Default for Doubly<T> {
    /// Construct an empty instance with no elements.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let instance = Doubly::<()>::default();
    ///
    /// assert_eq!(instance.len(), 0);
    /// ```
    fn default() -> Self {
        Doubly {
            head: None,
            tail: None,
        }
    }
}

impl<T: Clone> Clone for Doubly<T> {
    /// Clone all contained elements into a new instance of [`Self`].
    ///
    /// # Panics
    /// The Rust runtime might abort if allocation fails, panics otherwise.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(N) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let original = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// let clone = original.clone();
    ///
    /// assert_eq!(clone, original);
    /// ```
    fn clone(&self) -> Self {
        self.iter().cloned().collect()
    }
}

impl<T: PartialEq> PartialEq for Doubly<T> {
    /// Query if `other` has the same elements in the same order.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let elements = [0, 1, 2, 3, 4, 5];
    ///
    /// let first = Doubly::from_iter(elements.iter().copied());
    /// let second = Doubly::from_iter(elements.iter().copied());
    ///
    /// assert_eq!(first, second);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T: Eq> Eq for Doubly<T> {}

impl<T: core::fmt::Debug> core::fmt::Debug for Doubly<T> {
    /// Print to `output` a formatted list of the contained elements.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Doubly::from_iter(expected.iter().copied());
    ///
    /// assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    /// ```
    fn fmt(&self, output: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        output.debug_list().entries(self.iter()).finish()
    }
}

impl<T> core::ops::Index<usize> for Doubly<T> {
    type Output = T;

    /// Obtain an immutable reference to the element at position `index`.
    ///
    /// # Panics
    /// This method has the precondition that `index` is within bounds.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Doubly::from_iter(expected.iter().copied());
    ///
    /// for index in 0..expected.len() {
    ///     use core::ops::Index;
    ///
    ///     assert_eq!(actual.index(index), expected.index(index));
    /// }
    /// ```
    fn index(&self, index: usize) -> &Self::Output {
        let mut next = self.head;

        for _ in 0..index {
            if let Some(current) = next {
                // SAFETY: immutable references can alias.
                let current = unsafe { current.as_ref() };

                next = current.successor;
            } else {
                break;
            }
        }

        next.map_or_else(
            || panic!("index out of bounds"),
            |node| {
                // SAFETY: immutable references can alias.
                let node = unsafe { node.as_ref() };

                &node.element
            },
        )
    }
}

impl<T> core::ops::IndexMut<usize> for Doubly<T> {
    /// Obtain a mutable reference to the element at position `index`.
    ///
    /// # Safety
    /// This method does _NOT_ prevent creating aliasing mutable references
    /// if multiple calls are made with the same `index`.
    ///
    /// # Panics
    /// This method has the precondition that `index` is within bounds.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    /// let mut actual = Doubly::from_iter(expected.iter().copied());
    ///
    /// for index in 0..expected.len() {
    ///     use core::ops::IndexMut;
    ///
    ///     assert_eq!(actual.index_mut(index), expected.index_mut(index));
    /// }
    /// ```
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let mut next = self.head;

        for _ in 0..index {
            if let Some(mut current) = next {
                // SAFETY: no other references to this node exist.
                // However, mutable references to the element may.
                // That means this is _probably_ undefined behaviour.
                let current = unsafe { current.as_mut() };

                next = current.successor;
            } else {
                break;
            }
        }

        next.map_or_else(
            || panic!("index out of bounds"),
            |mut node| {
                // SAFETY: if `index` is unique, then so is this reference.
                let node = unsafe { node.as_mut() };

                &mut node.element
            },
        )
    }
}

impl<T> Iterator for Doubly<T> {
    type Item = T;

    /// Move the front/first element out of [`Self`], if any are contained.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]).into_iter();
    ///
    /// assert_eq!(instance.next(), Some(0));
    /// assert_eq!(instance.next(), Some(1));
    /// assert_eq!(instance.next(), Some(2));
    /// assert_eq!(instance.next(), Some(3));
    /// assert_eq!(instance.next(), Some(4));
    /// assert_eq!(instance.next(), Some(5));
    /// assert_eq!(instance.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        self.head.take().map(|removed| {
            // SAFETY:
            // * we own the node.
            // * there are no references to the node to invalidate.
            // * the node was allocated via `Box` and `into_raw`.
            let mut removed = unsafe { Box::from_raw(removed.as_ptr()) };

            debug_assert_eq!(removed.predecessor, None, "no predecessor to update");

            if let Some(successor) = removed.successor.take() {
                let successor = self.head.insert(successor);

                // SAFETY: no other references to this node exist.
                let successor = unsafe { successor.as_mut() };

                successor.predecessor = None;
            } else {
                self.tail = None;
            }

            removed.element
        })
    }

    /// Query how many elements are contained.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]).into_iter();
    ///
    /// assert_eq!(instance.size_hint(), (6, Some(6)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        let count = self.count();

        (count, Some(count))
    }
}

impl<T> DoubleEndedIterator for Doubly<T> {
    /// Move the back/last element out of [`Self`], if any are contained.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]).into_iter();
    ///
    /// assert_eq!(instance.next_back(), Some(5));
    /// assert_eq!(instance.next_back(), Some(4));
    /// assert_eq!(instance.next_back(), Some(3));
    /// assert_eq!(instance.next_back(), Some(2));
    /// assert_eq!(instance.next_back(), Some(1));
    /// assert_eq!(instance.next_back(), Some(0));
    /// assert_eq!(instance.next_back(), None);
    /// ```
    fn next_back(&mut self) -> Option<Self::Item> {
        self.tail.take().map(|removed| {
            // SAFETY:
            // * we own the node.
            // * there are no references to the node to invalidate.
            // * the node was allocated via `Box` and `into_raw`.
            let mut removed = unsafe { Box::from_raw(removed.as_ptr()) };

            debug_assert_eq!(removed.successor, None, "no successor to update");

            if let Some(predecessor) = removed.predecessor.take() {
                let predecessor = self.tail.insert(predecessor);

                // SAFETY: no other references to this node exist.
                let predecessor = unsafe { predecessor.as_mut() };

                predecessor.successor = None;
            } else {
                self.head = None;
            }

            removed.element
        })
    }
}

impl<T> ExactSizeIterator for Doubly<T> {}

impl<T> core::iter::FusedIterator for Doubly<T> {}

impl<T> Extend<T> for Doubly<T> {
    /// Move `elements` to the end of [`Self`], maintaining order.
    ///
    /// # Panics
    /// The Rust runtime might abort if allocation fails, panics otherwise.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2]);
    ///
    /// instance.extend([3, 4, 5]);
    ///
    /// assert!(instance.eq([0, 1, 2, 3, 4, 5]));
    /// ```
    fn extend<Iter: IntoIterator<Item = T>>(&mut self, elements: Iter) {
        for element in elements {
            assert!(self.append(element).is_ok(), "allocation failed");
        }
    }
}

impl<T> FromIterator<T> for Doubly<T> {
    /// Construct an instance with `elements`.
    ///
    /// # Panics
    /// The Rust runtime might abort if allocation fails, panics otherwise.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(N) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Doubly::from_iter(expected.iter().copied());
    ///
    /// assert!(actual.eq(expected));
    /// ```
    fn from_iter<Iter: IntoIterator<Item = T>>(elements: Iter) -> Self {
        let mut instance = Doubly::<T>::default();

        instance.extend(elements);

        instance
    }
}

impl<T> Collection for Doubly<T> {
    type Element = T;

    /// Query how many elements are contained.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::Collection;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(instance.count(), 6);
    /// ```
    fn count(&self) -> usize {
        let mut count: usize = 0;

        let mut next = self.head;

        while let Some(current) = next {
            if let Some(incremented) = count.checked_add(1) {
                count = incremented;
            } else {
                unreachable!("more elements than supported by the address space (usize::MAX)");
            }

            // SAFETY: immutable references can alias.
            let current = unsafe { current.as_ref() };

            next = current.successor;
        }

        count
    }
}

impl<T> Linear for Doubly<T> {
    /// Iterate over the elements by immutable reference.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let instance = Doubly::from_iter(expected.iter().copied());
    ///
    /// assert!(instance.iter().eq(expected.iter()));
    /// ```
    fn iter(
        &self,
    ) -> impl DoubleEndedIterator<Item = &Self::Element> + ExactSizeIterator + core::iter::FusedIterator
    {
        Iter {
            front: self.head,
            back: self.tail,
            lifetime: core::marker::PhantomData,
        }
    }

    /// Iterate over the elements by mutable reference.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    /// let mut instance = Doubly::from_iter(expected.iter().copied());
    ///
    /// assert!(instance.iter_mut().eq(expected.iter_mut()));
    /// ```
    fn iter_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = &mut Self::Element>
           + ExactSizeIterator
           + core::iter::FusedIterator {
        IterMut {
            front: self.head,
            back: self.tail,
            lifetime: core::marker::PhantomData,
        }
    }

    /// Obtain an immutable reference to the element at position `index`.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let actual = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(actual.at(0), Some(&0));
    /// assert_eq!(actual.at(1), Some(&1));
    /// assert_eq!(actual.at(2), Some(&2));
    /// assert_eq!(actual.at(3), Some(&3));
    /// assert_eq!(actual.at(4), Some(&4));
    /// assert_eq!(actual.at(5), Some(&5));
    /// assert_eq!(actual.at(6), None);
    /// ```
    fn at(&self, index: usize) -> Option<&Self::Element> {
        let mut next = self.head;

        for _ in 0..index {
            if let Some(current) = next {
                // SAFETY: immutable references can alias.
                let current = unsafe { current.as_ref() };

                next = current.successor;
            } else {
                break;
            }
        }

        next.map(|node| {
            // SAFETY: immutable references can alias.
            let node = unsafe { node.as_ref() };

            &node.element
        })
    }

    /// Obtain a mutable reference to the element at position `index`.
    ///
    /// # Safety
    /// This method does _NOT_ prevent creating aliasing mutable references
    /// if multiple calls are made with the same `index`.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut actual = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(actual.at_mut(0), Some(&mut 0));
    /// assert_eq!(actual.at_mut(1), Some(&mut 1));
    /// assert_eq!(actual.at_mut(2), Some(&mut 2));
    /// assert_eq!(actual.at_mut(3), Some(&mut 3));
    /// assert_eq!(actual.at_mut(4), Some(&mut 4));
    /// assert_eq!(actual.at_mut(5), Some(&mut 5));
    /// assert_eq!(actual.at_mut(6), None);
    /// ```
    fn at_mut(&mut self, index: usize) -> Option<&mut Self::Element> {
        let mut next = self.head;

        for _ in 0..index {
            if let Some(mut current) = next {
                // SAFETY: no other references to this node exist.
                // However, mutable references to the element may.
                // That means this is _probably_ undefined behaviour.
                let current = unsafe { current.as_mut() };

                next = current.successor;
            } else {
                break;
            }
        }

        next.map(|mut node| {
            // SAFETY: if `index` is unique, then so is this reference.
            let node = unsafe { node.as_mut() };

            &mut node.element
        })
    }

    /// Query the element considered to be at the front, the first element.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(instance.first(), Some(&0));
    /// ```
    fn first(&self) -> Option<&Self::Element> {
        self.head.map(|first| {
            // SAFETY: immutable references can alias.
            let first = unsafe { first.as_ref() };

            &first.element
        })
    }

    /// Query the element considered to be at the back, the last element.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(Linear::last(&instance), Some(&5));
    /// ```
    fn last(&self) -> Option<&Self::Element> {
        self.tail.map(|last| {
            // SAFETY: immutable references can alias.
            let last = unsafe { last.as_ref() };

            &last.element
        })
    }

    /// Obtain a reference to the element at the front, the first element.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(instance.first_mut(), Some(&mut 0));
    /// ```
    fn first_mut(&mut self) -> Option<&mut Self::Element> {
        self.head.map(|mut first| {
            // SAFETY: no other references to this node will be created.
            let first = unsafe { first.as_mut() };

            &mut first.element
        })
    }

    /// Obtain a reference to the element at the back, the last element.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(instance.last_mut(), Some(&mut 5));
    /// ```
    fn last_mut(&mut self) -> Option<&mut Self::Element> {
        self.tail.map(|mut last| {
            // SAFETY: no other references to this node will be created.
            let last = unsafe { last.as_mut() };

            &mut last.element
        })
    }
}

impl<T> List for Doubly<T> {
    /// Move an `element` into [`Self`] at position `index`.
    ///
    /// # Panics
    /// The Rust runtime might abort if allocation fails, panics otherwise.
    ///
    /// # Performance
    /// This method takes O(N) times and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 4, 5]);
    ///
    /// assert!(instance.insert(3, 3).is_ok_and(|inserted| inserted == &3));
    /// assert!(instance.eq([0, 1, 2, 3, 4, 5]));
    /// ```
    fn insert(
        &mut self,
        index: usize,
        element: Self::Element,
    ) -> Result<&mut Self::Element, Self::Element> {
        let mut next = self.head;

        for _ in 0..index.saturating_sub(1) {
            if let Some(mut current) = next {
                // SAFETY: no other references to this node exist.
                let current = unsafe { current.as_mut() };

                next = current.successor;
            } else {
                return Err(element);
            }
        }

        let allocation = Box::into_raw(Box::new(Node {
            element,
            predecessor: None,
            successor: None,
        }));

        // SAFETY: Only null if allocation failed, which panics before this.
        let mut allocation = unsafe { NonNull::new_unchecked(allocation) };

        // SAFETY: no other references to this node exist.
        let new = unsafe { allocation.as_mut() };

        if let Some(mut existing) = next {
            if index == 0 {
                self.head = Some(allocation);

                new.successor = Some(existing);

                // SAFETY: no other references to this node exist.
                let successor = unsafe { existing.as_mut() };

                successor.predecessor = Some(allocation);
            } else {
                new.predecessor = Some(existing);

                // SAFETY: no other references to this node exist.
                let predecessor = unsafe { existing.as_mut() };

                if let Some(mut successor) = predecessor.successor {
                    new.successor = Some(successor);

                    // SAFETY: no other references to this node exist.
                    let successor = unsafe { successor.as_mut() };

                    successor.predecessor = Some(allocation);
                } else {
                    self.tail = Some(allocation);
                }

                predecessor.successor = Some(allocation);
            }
        } else {
            self.head = Some(allocation);
            self.tail = Some(allocation);
        }

        Ok(&mut new.element)
    }

    /// Move the element at `index` out of [`Self`], if it exists.
    ///
    /// # Performance
    /// This method takes O(N) times and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert!(instance.remove(3).is_some_and(|inserted| inserted == 3));
    /// assert!(instance.eq([0, 1, 2, 4, 5]));
    /// ```
    fn remove(&mut self, index: usize) -> Option<Self::Element> {
        let mut next = &mut self.head;

        for _ in 0..index {
            if let Some(mut current) = *next {
                // SAFETY: no other references to this node exist.
                let current = unsafe { current.as_mut() };

                next = &mut current.successor;
            } else {
                return None;
            }
        }

        // SAFETY:
        // * we own the node.
        // * there are no references to the node to invalidate.
        // * the node was allocated via `Box` and `into_raw`.
        let mut removed = unsafe { Box::from_raw(next.take()?.as_ptr()) };

        if let Some(mut successor) = removed.successor {
            // SAFETY: no other references to this node exist.
            let successor = unsafe { successor.as_mut() };

            successor.predecessor = removed.predecessor;
        } else {
            self.tail = removed.predecessor.take();
        }

        if let Some(mut predecessor) = removed.predecessor {
            // SAFETY: no other references to this node exist.
            let predecessor = unsafe { predecessor.as_mut() };

            predecessor.successor = removed.successor;
        } else {
            self.head = removed.successor.take();
        }

        Some(removed.element)
    }

    /// Move an `element` into a new node at the front to become the first.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([1, 2, 3, 4, 5]);
    ///
    /// instance.prepend(0);
    ///
    /// assert!(instance.eq([0, 1, 2, 3, 4, 5]));
    /// ```
    fn prepend(&mut self, element: Self::Element) -> Result<&mut Self::Element, Self::Element> {
        let allocation = Box::into_raw(Box::new(Node {
            element,
            predecessor: None,
            successor: self.head.take(),
        }));

        // SAFETY: Only null if allocation failed, which panics before this.
        let mut allocation = unsafe { NonNull::new_unchecked(allocation) };

        // SAFETY: no other references to this node exist.
        let new = unsafe { allocation.as_mut() };

        self.head = Some(allocation);

        if let Some(mut successor) = new.successor {
            // SAFETY: no other references to this node exist.
            let successor = unsafe { successor.as_mut() };

            successor.predecessor = Some(allocation);
        }

        if self.tail.is_none() {
            self.tail = Some(allocation);
        }

        Ok(&mut new.element)
    }

    /// Move an `element` into a new node at the back to become the last.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4]);
    ///
    /// instance.append(5);
    ///
    /// assert!(instance.eq([0, 1, 2, 3, 4, 5]));
    /// ```
    fn append(&mut self, element: Self::Element) -> Result<&mut Self::Element, Self::Element> {
        let allocation = Box::into_raw(Box::new(Node {
            element,
            predecessor: self.tail.take(),
            successor: None,
        }));

        // SAFETY: Only null if allocation failed, which panics before this.
        let mut allocation = unsafe { NonNull::new_unchecked(allocation) };

        // SAFETY: no other references to this node exist.
        let new = unsafe { allocation.as_mut() };

        self.tail = Some(allocation);

        if let Some(mut predecessor) = new.predecessor {
            // SAFETY: no other references to this node exist.
            let predecessor = unsafe { predecessor.as_mut() };

            predecessor.successor = Some(allocation);
        }

        if self.head.is_none() {
            self.head = Some(allocation);
        }

        Ok(&mut new.element)
    }

    /// Remove the element at the front, the first element, if any.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(instance.front(), Some(0));
    /// assert_eq!(instance.front(), Some(1));
    /// assert_eq!(instance.front(), Some(2));
    /// assert_eq!(instance.front(), Some(3));
    /// assert_eq!(instance.front(), Some(4));
    /// assert_eq!(instance.front(), Some(5));
    /// assert_eq!(instance.front(), None);
    /// ```
    fn front(&mut self) -> Option<Self::Element> {
        let removed = self.head.take()?;

        // SAFETY:
        // * we own the node.
        // * there are no references to the node to invalidate.
        // * the node was allocated via `Box` and `into_raw`.
        let removed = unsafe { Box::from_raw(removed.as_ptr()) };

        if let Some(mut successor) = removed.successor {
            self.head = Some(successor);

            // SAFETY: no other references to this node exist.
            let successor = unsafe { successor.as_mut() };

            successor.predecessor = None;
        } else {
            self.tail = None;
        }

        Some(removed.element)
    }

    /// Remove the element at the back, the last element, if any.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(instance.back(), Some(5));
    /// assert_eq!(instance.back(), Some(4));
    /// assert_eq!(instance.back(), Some(3));
    /// assert_eq!(instance.back(), Some(2));
    /// assert_eq!(instance.back(), Some(1));
    /// assert_eq!(instance.back(), Some(0));
    /// assert_eq!(instance.back(), None);
    /// ```
    fn back(&mut self) -> Option<Self::Element> {
        let removed = self.tail.take()?;

        // SAFETY:
        // * we own the node.
        // * there are no references to the node to invalidate.
        // * the node was allocated via `Box` and `into_raw`.
        let removed = unsafe { Box::from_raw(removed.as_ptr()) };

        if let Some(mut predecessor) = removed.predecessor {
            self.tail = Some(predecessor);

            // SAFETY: no other references to this node exist.
            let predecessor = unsafe { predecessor.as_mut() };

            predecessor.successor = None;
        } else {
            self.head = None;
        }

        Some(removed.element)
    }

    /// Move the elements at indexes within `range` out, if they exist.
    ///
    /// # Performance
    /// This method takes O(N) times and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert!(instance.drain(1..=4).eq([1, 2, 3, 4]));
    /// assert!(instance.eq([0, 5]));
    /// ```
    fn drain(
        &mut self,
        range: impl core::ops::RangeBounds<usize>,
    ) -> impl DoubleEndedIterator<Item = Self::Element> + ExactSizeIterator {
        // These values denote the range and do not correspond to elements.
        let (offset, remaining) = (|| {
            let offset = match range.start_bound() {
                core::ops::Bound::Included(start) => *start,
                core::ops::Bound::Excluded(start) => {
                    if let Some(incremented) = start.checked_add(1) {
                        incremented
                    } else {
                        return (0, 0);
                    }
                }
                core::ops::Bound::Unbounded => 0,
            };

            let remaining = match range.end_bound() {
                core::ops::Bound::Included(end) => end.abs_diff(offset).saturating_add(1),
                core::ops::Bound::Excluded(end) => end.abs_diff(offset),
                core::ops::Bound::Unbounded => usize::MAX.abs_diff(offset),
            };

            (offset, remaining)
        })();

        let front = {
            let mut next = &mut self.head;

            for _ in 0..offset {
                if let Some(mut current) = *next {
                    // SAFETY: no other references to this node exist.
                    let current = unsafe { current.as_mut() };

                    next = &mut current.successor;
                } else {
                    break;
                }
            }

            next
        };

        let (back, remaining) = {
            let mut count: usize = 0;

            let mut next = &mut *front;

            for _ in 0..remaining {
                if let Some(mut current) = *next {
                    if let Some(incremented) = count.checked_add(1) {
                        count = incremented;
                    } else {
                        unreachable!(
                            "more elements than supported by the address space (usize::MAX)"
                        );
                    }

                    // SAFETY: no other references to this node exist.
                    let node = unsafe { current.as_mut() };

                    next = &mut node.successor;
                } else {
                    break;
                }
            }

            if let Some(mut successor) = *next {
                // SAFETY: no other references to this node exist.
                let successor = unsafe { successor.as_mut() };

                (&mut successor.predecessor, count)
            } else {
                (&mut self.tail, count)
            }
        };

        Drain {
            front,
            back,
            remaining,
        }
    }

    /// Move the elements matching some `predicate` out, if they exist.
    ///
    /// # Performance
    /// This method takes O(1) times and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert!(instance.withdraw(|element| element % 2 == 0).eq([0, 2, 4]));
    /// assert!(instance.eq([1, 3, 5]));
    /// ```
    fn withdraw(
        &mut self,
        predicate: impl FnMut(&Self::Element) -> bool,
    ) -> impl DoubleEndedIterator<Item = Self::Element> {
        Withdraw {
            front: &mut self.head,
            back: &mut self.tail,
            exhausted: false,
            predicate,
        }
    }
}

impl<T> Stack for Doubly<T> {
    /// Move an `element` on the top of the stack.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Stack;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::<usize>::default();
    ///
    /// instance.push(5).expect("successful allocation");
    /// instance.push(4).expect("successful allocation");
    /// instance.push(3).expect("successful allocation");
    /// instance.push(2).expect("successful allocation");
    /// instance.push(1).expect("successful allocation");
    /// instance.push(0).expect("successful allocation");
    ///
    /// assert!(instance.eq([0, 1, 2, 3, 4, 5]));
    /// ```
    fn push(&mut self, element: Self::Element) -> Result<&mut Self::Element, Self::Element> {
        self.prepend(element)
    }

    /// Move out the element at the top of the stack.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Stack;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(instance.pop(), Some(0));
    /// assert_eq!(instance.pop(), Some(1));
    /// assert_eq!(instance.pop(), Some(2));
    /// assert_eq!(instance.pop(), Some(3));
    /// assert_eq!(instance.pop(), Some(4));
    /// assert_eq!(instance.pop(), Some(5));
    /// assert_eq!(instance.pop(), None);
    /// ```
    fn pop(&mut self) -> Option<Self::Element> {
        self.front()
    }

    /// Query the element at the top of the stack.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Stack;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(instance.peek(), Some(&0));
    /// ```
    fn peek(&self) -> Option<&Self::Element> {
        self.first()
    }
}

/// Immutable iterator over a [`Doubly`].
struct Iter<'a, T> {
    /// The next element to yield from the front, if any.
    front: Option<NonNull<Node<T>>>,

    /// The next element to yield from the back, if any.
    back: Option<NonNull<Node<T>>>,

    /// Bind lifetime to underlying owner.
    lifetime: core::marker::PhantomData<&'a T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    /// Obtain the next element from the front, if any.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut instance = underlying.iter();
    ///
    /// assert_eq!(instance.next(), Some(&0));
    /// assert_eq!(instance.next(), Some(&1));
    /// assert_eq!(instance.next(), Some(&2));
    /// assert_eq!(instance.next(), Some(&3));
    /// assert_eq!(instance.next(), Some(&4));
    /// assert_eq!(instance.next(), Some(&5));
    /// assert_eq!(instance.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        self.front.map(|next| {
            // SAFETY: immutable references can alias.
            let next = unsafe { next.as_ref() };

            if let Some(back) = self.back {
                if core::ptr::addr_eq(next, back.as_ptr()) {
                    self.front = None;
                    self.back = None;
                } else {
                    self.front = next.successor;
                }
            } else {
                unreachable!("at least the current node remaining");
            }

            &next.element
        })
    }

    /// Query how many elements have yet to be yielded.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let instance = underlying.iter();
    ///
    /// assert_eq!(instance.size_hint(), (6, Some(6)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        let mut count: usize = 0;

        let mut next = self.front;

        while let Some(current) = next {
            if let Some(incremented) = count.checked_add(1) {
                count = incremented;
            } else {
                unreachable!("more elements than supported by the address space (usize::MAX)");
            }

            if let Some(sentinel) = self.back {
                if current == sentinel {
                    break;
                }

                // SAFETY: immutable references can alias.
                let current = unsafe { current.as_ref() };

                next = current.successor;
            } else {
                unreachable!("at least the current node remaining")
            }
        }

        (count, Some(count))
    }
}

impl<T> DoubleEndedIterator for Iter<'_, T> {
    /// Obtain the next element from the back, if any.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut instance = underlying.iter().rev();
    ///
    /// assert_eq!(instance.next(), Some(&5));
    /// assert_eq!(instance.next(), Some(&4));
    /// assert_eq!(instance.next(), Some(&3));
    /// assert_eq!(instance.next(), Some(&2));
    /// assert_eq!(instance.next(), Some(&1));
    /// assert_eq!(instance.next(), Some(&0));
    /// assert_eq!(instance.next(), None);
    /// ```
    fn next_back(&mut self) -> Option<Self::Item> {
        self.back.map(|next| {
            // SAFETY: immutable references can alias.
            let next = unsafe { next.as_ref() };

            if let Some(front) = self.front {
                if core::ptr::addr_eq(next, front.as_ptr()) {
                    self.front = None;
                    self.back = None;
                } else {
                    self.back = next.predecessor;
                }
            } else {
                unreachable!("at least the current node remaining");
            }

            &next.element
        })
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {}

impl<T> core::iter::FusedIterator for Iter<'_, T> {}

/// Mutable iterator over a [`Doubly`].
struct IterMut<'a, T> {
    /// The next element to yield from the front, if any.
    front: Option<NonNull<Node<T>>>,

    /// The next element to yield from the back, if any.
    back: Option<NonNull<Node<T>>>,

    /// Bind lifetime to underlying owner.
    lifetime: core::marker::PhantomData<&'a mut T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    /// Obtain the next element from the front, if any.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut instance = underlying.iter_mut();
    ///
    /// assert_eq!(instance.next(), Some(&mut 0));
    /// assert_eq!(instance.next(), Some(&mut 1));
    /// assert_eq!(instance.next(), Some(&mut 2));
    /// assert_eq!(instance.next(), Some(&mut 3));
    /// assert_eq!(instance.next(), Some(&mut 4));
    /// assert_eq!(instance.next(), Some(&mut 5));
    /// assert_eq!(instance.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        self.front.map(|mut next| {
            // SAFETY: no other references to this node will be created.
            let next = unsafe { next.as_mut() };

            if let Some(back) = self.back {
                if core::ptr::addr_eq(next, back.as_ptr()) {
                    self.front = None;
                    self.back = None;
                } else {
                    self.front = next.successor;
                }
            } else {
                unreachable!("at least the current node remaining");
            }

            &mut next.element
        })
    }

    /// Query how many elements have yet to be yielded.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let instance = underlying.iter_mut();
    ///
    /// assert_eq!(instance.size_hint(), (6, Some(6)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        let mut count: usize = 0;

        let mut next = self.front;

        while let Some(current) = next {
            if let Some(incremented) = count.checked_add(1) {
                count = incremented;
            } else {
                unreachable!("more elements than supported by the address space (usize::MAX)");
            }

            if let Some(sentinel) = self.back {
                if current == sentinel {
                    break;
                }

                // SAFETY: no other active references to this node.
                let current = unsafe { current.as_ref() };

                next = current.successor;
            } else {
                unreachable!("at least the current node remaining")
            }
        }

        (count, Some(count))
    }
}

impl<T> DoubleEndedIterator for IterMut<'_, T> {
    /// Obtain the next element from the back, if any.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut instance = underlying.iter_mut().rev();
    ///
    /// assert_eq!(instance.next(), Some(&mut 5));
    /// assert_eq!(instance.next(), Some(&mut 4));
    /// assert_eq!(instance.next(), Some(&mut 3));
    /// assert_eq!(instance.next(), Some(&mut 2));
    /// assert_eq!(instance.next(), Some(&mut 1));
    /// assert_eq!(instance.next(), Some(&mut 0));
    /// assert_eq!(instance.next(), None);
    /// ```
    fn next_back(&mut self) -> Option<Self::Item> {
        self.back.map(|mut next| {
            // SAFETY: no other references to this node will be created.
            let next = unsafe { next.as_mut() };

            if let Some(front) = self.front {
                if core::ptr::addr_eq(next, front.as_ptr()) {
                    self.front = None;
                    self.back = None;
                } else {
                    self.back = next.predecessor;
                }
            } else {
                unreachable!("at least the current node remaining");
            }

            &mut next.element
        })
    }
}

impl<T> ExactSizeIterator for IterMut<'_, T> {}

impl<T> core::iter::FusedIterator for IterMut<'_, T> {}

/// [`Iterator`] to yield elements within an index range from [`Doubly`].
///
/// See [`Doubly::drain`].
struct Drain<'a, T> {
    /// The next (front) element to remove, if any.
    front: &'a mut Option<NonNull<Node<T>>>,

    /// The next (back) element to remove, if any.
    back: &'a mut Option<NonNull<Node<T>>>,

    /// The maximum amount of elements yet to be yielded.
    remaining: usize,
}

impl<T> Drop for Drain<'_, T> {
    /// Drop all elements yet to be yielded.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// drop(instance.drain(1..=4));
    ///
    /// assert!(instance.eq([0, 5]));
    /// ```
    fn drop(&mut self) {
        self.for_each(drop);
    }
}

impl<T> Iterator for Drain<'_, T> {
    type Item = T;

    /// Obtain the next element from the front, if any exists.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut instance = underlying.drain(1..=4);
    ///
    /// assert_eq!(instance.next(), Some(1));
    /// assert_eq!(instance.next(), Some(2));
    /// assert_eq!(instance.next(), Some(3));
    /// assert_eq!(instance.next(), Some(4));
    /// assert_eq!(instance.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        self.remaining.checked_sub(1).and_then(|decremented| {
            self.remaining = decremented;

            let mut ptr = self.front.take()?;

            {
                // SAFETY: no other references to this node exist.
                let removed = unsafe { ptr.as_mut() };

                if let Some(back) = *self.back {
                    if ptr == back {
                        *self.back = removed.predecessor;
                    } else if let Some(mut successor) = removed.successor {
                        // SAFETY: does not alias back, so unique reference.
                        let successor = unsafe { successor.as_mut() };

                        successor.predecessor = removed.predecessor.take();
                    } else {
                        unreachable!("either last node, or some successor");
                    }
                } else {
                    unreachable!("at least the current node remaining");
                }

                *self.front = removed.successor.take();
            }

            // SAFETY:
            // * we own the node.
            // * there are no references to the node to invalidate.
            // * the node was allocated via `Box` and `into_raw`.
            let removed = unsafe { Box::from_raw(ptr.as_ptr()) };

            Some(removed.element)
        })
    }

    /// Query how many elements have yet to be yielded.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let instance = underlying.drain(1..=4);
    ///
    /// assert_eq!(instance.size_hint(), (4, Some(4)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<T> DoubleEndedIterator for Drain<'_, T> {
    /// Obtain the next element from the back, if any exists.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut instance = underlying.drain(1..=4).rev();
    ///
    /// assert_eq!(instance.next(), Some(4));
    /// assert_eq!(instance.next(), Some(3));
    /// assert_eq!(instance.next(), Some(2));
    /// assert_eq!(instance.next(), Some(1));
    /// assert_eq!(instance.next(), None);
    /// ```
    fn next_back(&mut self) -> Option<Self::Item> {
        self.remaining.checked_sub(1).and_then(|decremented| {
            self.remaining = decremented;

            let mut removed = self.back.take()?;

            {
                // SAFETY: no other references to this node exist.
                let node = unsafe { removed.as_mut() };

                if let Some(front) = *self.front {
                    if removed == front {
                        *self.front = node.successor;
                    } else if let Some(mut predecessor) = node.predecessor {
                        // SAFETY: does not alias front, so unique reference.
                        let predecessor = unsafe { predecessor.as_mut() };

                        predecessor.successor = node.successor.take();
                    } else {
                        unreachable!("either last node, or some predecessor");
                    }
                } else {
                    unreachable!("at least the current node remaining");
                }

                *self.back = node.predecessor.take();
            }

            // SAFETY:
            // * we own the node.
            // * there are no references to the node to invalidate.
            // * the node was allocated via `Box` and `into_raw`.
            let removed = unsafe { Box::from_raw(removed.as_ptr()) };

            Some(removed.element)
        })
    }
}

impl<T> ExactSizeIterator for Drain<'_, T> {}

impl<T> core::iter::FusedIterator for Drain<'_, T> {}

/// [`Iterator`] to yield elements matching a predicate from [`Doubly`].
///
/// See [`Doubly::withdraw`].
struct Withdraw<'a, T, F: FnMut(&T) -> bool> {
    /// The next from the back to query with the predicate.
    front: &'a mut Option<NonNull<Node<T>>>,

    /// The next from the back to query with the predicate.
    back: &'a mut Option<NonNull<Node<T>>>,

    /// If all elements have been queried.
    exhausted: bool,

    /// The predicate based upon which elements are withdrawn.
    predicate: F,
}

impl<T, F: FnMut(&T) -> bool> Drop for Withdraw<'_, T, F> {
    /// Drop all elements yet to be yielded.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// drop(instance.withdraw(|element| element % 2 == 0));
    ///
    /// assert!(instance.eq([1, 3, 5]));
    /// ```
    fn drop(&mut self) {
        self.for_each(drop);
    }
}

impl<T, F: FnMut(&T) -> bool> Iterator for Withdraw<'_, T, F> {
    type Item = T;

    /// Obtain the next element from the front, if any exists.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut instance = underlying.withdraw(|element| element % 2 == 0);
    ///
    /// assert_eq!(instance.next(), Some(0));
    /// assert_eq!(instance.next(), Some(2));
    /// assert_eq!(instance.next(), Some(4));
    /// assert_eq!(instance.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        while let Some(mut removed) = self.front.take() {
            // SAFETY: no other references to this node exists.
            let node = unsafe { removed.as_mut() };

            if (self.predicate)(&node.element) {
                if let Some(back) = *self.back {
                    if removed == back {
                        *self.back = node.predecessor;
                    } else if let Some(mut successor) = node.successor {
                        // SAFETY: does not alias back, so unique reference.
                        let successor = unsafe { successor.as_mut() };

                        successor.predecessor = node.predecessor.take();
                    } else {
                        unreachable!("either last node, or some successor");
                    }
                } else {
                    unreachable!("at least the current node remaining");
                }

                *self.front = node.successor.take();

                // SAFETY:
                // * we own the node.
                // * there are no references to the node to invalidate.
                // * the node was allocated via `Box` and `into_raw`.
                let removed = unsafe { Box::from_raw(removed.as_ptr()) };

                return Some(removed.element);
            }

            *self.front = Some(removed);
            self.front = &mut node.successor;

            if let Some(back) = *self.back {
                if removed == back {
                    self.exhausted = true;

                    break;
                }
            } else {
                unreachable!("at least the current node remaining");
            }
        }

        self.exhausted = true;

        None
    }

    /// Query how many elements have yet to be yielded.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let instance = underlying.withdraw(|element| element % 2 == 0);
    ///
    /// assert_eq!(instance.size_hint(), (0, Some(6)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        let mut count: usize = 0;

        let mut next = *self.front;

        while let Some(current) = next {
            if let Some(sentinel) = *self.back {
                if let Some(incremented) = count.checked_add(1) {
                    count = incremented;
                } else {
                    unreachable!("more elements than supported by the address space (usize::MAX)");
                }

                if current == sentinel {
                    break;
                }

                // SAFETY: no other references to this node exist.
                let current = unsafe { current.as_ref() };

                next = current.successor;
            }
        }

        (0, Some(count))
    }
}

impl<T, F: FnMut(&T) -> bool> DoubleEndedIterator for Withdraw<'_, T, F> {
    /// Obtain the next element from the back, if any exists.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Doubly;
    ///
    /// let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut instance = underlying.withdraw(|element| element % 2 == 0).rev();
    ///
    /// assert_eq!(instance.next(), Some(4));
    /// assert_eq!(instance.next(), Some(2));
    /// assert_eq!(instance.next(), Some(0));
    /// assert_eq!(instance.next(), None);
    /// ```
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.exhausted {
            return None;
        }

        while let Some(mut removed) = self.back.take() {
            // SAFETY: no other references to this node exist.
            let node = unsafe { removed.as_mut() };

            if (self.predicate)(&node.element) {
                if let Some(front) = *self.front {
                    if removed == front {
                        *self.front = node.successor;
                    } else if let Some(mut predecessor) = node.predecessor {
                        // SAFETY: does not alias front, so unique reference.
                        let predecessor = unsafe { predecessor.as_mut() };

                        predecessor.successor = node.successor.take();
                    } else {
                        unreachable!("either last node, or some predecessor");
                    }
                } else {
                    unreachable!("at least the current node remaining");
                }

                *self.back = node.predecessor.take();

                // SAFETY:
                // * we own the node.
                // * there are no references to the node to invalidate.
                // * the node was allocated via `Box` and `into_raw`.
                let removed = unsafe { Box::from_raw(removed.as_ptr()) };

                return Some(removed.element);
            }

            *self.back = Some(removed);
            self.back = &mut node.predecessor;

            if let Some(front) = *self.front {
                if removed == front {
                    self.exhausted = true;

                    break;
                }
            } else {
                unreachable!("at least the current node remaining");
            }
        }

        self.exhausted = true;

        None
    }
}

impl<T, F: FnMut(&T) -> bool> ExactSizeIterator for Withdraw<'_, T, F> {}

impl<T, F: FnMut(&T) -> bool> core::iter::FusedIterator for Withdraw<'_, T, F> {}

#[cfg(test)]
#[allow(
    clippy::undocumented_unsafe_blocks,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::assertions_on_result_states,
    clippy::indexing_slicing
)]
mod test {
    use super::*;

    mod drop {
        use super::*;

        /// Mock element for drop tests.
        #[derive(Debug, Clone)]
        struct Droppable {
            /// A shared counter for the number of elements dropped.
            counter: alloc::rc::Rc<core::cell::RefCell<usize>>,
        }

        impl Drop for Droppable {
            /// Increment the shared counter upon drop.
            fn drop(&mut self) {
                _ = self.counter.replace_with(|old| old.wrapping_add(1));
            }
        }

        #[test]
        fn empty() {
            let instance = Doubly::<usize>::default();

            drop(instance);
        }

        #[test]
        fn zero_size_type() {
            let instance: Doubly<_> = [(), (), (), (), (), ()].into_iter().collect();

            drop(instance);
        }

        #[test]
        fn drops_elements() {
            const ELEMENTS: usize = 256;

            let dropped = alloc::rc::Rc::new(core::cell::RefCell::new(usize::default()));

            let mut actual = Doubly::<Droppable>::default();

            for _ in 0..ELEMENTS {
                _ = actual
                    .append(Droppable {
                        counter: alloc::rc::Rc::clone(&dropped),
                    })
                    .expect("successful allocation");
            }

            drop(actual);

            assert_eq!(dropped.take(), ELEMENTS);
        }
    }

    mod default {
        use super::*;

        #[test]
        fn has_no_elements() {
            let actual = Doubly::<()>::default();

            assert!(actual.head.is_none());
            assert!(actual.tail.is_none());
        }
    }

    mod clone {
        use super::*;

        #[test]
        fn has_elements() {
            let expected = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

            let actual = expected.clone();

            assert_eq!(actual.len(), expected.len());
        }

        #[test]
        fn is_equivalent() {
            let expected = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

            let actual = expected.clone();

            assert_eq!(actual, expected);
        }

        #[test]
        fn owns_elements() {
            let expected = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

            let actual = expected.clone();

            for (clone, original) in actual.iter().zip(expected.iter()) {
                assert!(!core::ptr::addr_eq(clone, original));
            }
        }
    }

    mod equality {
        use super::*;

        #[test]
        fn eq_when_same_elements() {
            let elements = [0, 1, 2, 3, 4, 5];

            let first: Doubly<_> = elements.iter().copied().collect();
            let second: Doubly<_> = elements.iter().copied().collect();

            assert_eq!(first, second);
        }

        #[test]
        fn ne_when_different_elements() {
            let first: Doubly<_> = [0].into_iter().collect();
            let second: Doubly<_> = [1].into_iter().collect();

            assert_ne!(first, second);
        }

        #[test]
        fn is_symmetric() {
            let elements = [0, 1, 2, 3, 4, 5];

            let first: Doubly<_> = elements.iter().copied().collect();
            let second: Doubly<_> = elements.iter().copied().collect();

            // `first == second` <=> `second == first`
            assert_eq!(first, second);
            assert_eq!(second, first);
        }

        #[test]
        fn is_transitive() {
            let elements = [0, 1, 2, 3, 4, 5];

            let first: Doubly<_> = elements.iter().copied().collect();
            let second: Doubly<_> = elements.iter().copied().collect();
            let third: Doubly<_> = elements.iter().copied().collect();

            // `first == second && second == third` => `first == third`
            assert_eq!(first, second);
            assert_eq!(second, third);
            assert_eq!(third, first);
        }

        #[test]
        fn is_reflexive() {
            let actual = Doubly::<()>::default();

            assert_eq!(actual, actual);
        }
    }

    mod fmt {
        use super::*;

        mod debug {
            use super::*;

            #[test]
            fn is_elements() {
                let expected = [0, 1, 2, 3, 4, 5];

                let actual: Doubly<_> = expected.iter().copied().collect();

                assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
            }
        }
    }

    mod index {
        use super::*;
        use core::ops::Index;

        #[test]
        fn correct_element() {
            let expected = [0, 1, 2, 3, 4, 5];
            let actual = Doubly::from_iter(expected);

            for (index, value) in expected.iter().enumerate() {
                assert_eq!(actual.index(index), value);
            }
        }

        #[test]
        #[should_panic = "index out of bounds"]
        fn panics_when_out_of_bounds() {
            let instance = Doubly::<()>::default();

            let _: &() = instance.index(0);
        }
    }

    mod index_mut {
        use super::*;
        use core::ops::IndexMut;

        #[test]
        fn correct_element() {
            let expected = [0, 1, 2, 3, 4, 5];
            let mut actual = Doubly::from_iter(expected);

            for (index, value) in expected.iter().enumerate() {
                assert_eq!(actual.index_mut(index), value);
            }
        }

        #[test]
        fn is_mutable() {
            let mut instance: Doubly<_> = [0, 1, 2, 3, 4, 5].into_iter().collect();

            for index in 0..instance.len() {
                *(instance.index_mut(index)) = 0;
            }

            for element in instance {
                assert_eq!(element, 0);
            }
        }

        #[test]
        #[should_panic = "index out of bounds"]
        fn panics_when_out_of_bounds() {
            let mut instance = Doubly::<()>::default();

            let _: &() = instance.index_mut(0);
        }
    }

    mod iterator {
        use super::*;

        struct FaultySizeHintIter<I> {
            data: core::iter::Copied<I>,
        }

        impl<'a, T: 'a + Copy, I> Iterator for FaultySizeHintIter<I>
        where
            I: Iterator<Item = &'a T>,
        {
            type Item = T;
            fn next(&mut self) -> Option<Self::Item> {
                self.data.next()
            }

            fn size_hint(&self) -> (usize, Option<usize>) {
                (usize::MAX, Some(usize::MAX))
            }
        }

        mod into {
            use super::*;

            #[test]
            fn element_count() {
                let expected = [0, 1, 2, 3, 4, 5];

                let actual: Doubly<_> = expected.iter().copied().collect();

                assert_eq!(actual.into_iter().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let expected = [0, 1, 2, 3, 4, 5];

                let actual: Doubly<_> = expected.iter().copied().collect();

                assert!(actual.into_iter().eq(expected));
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Doubly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.into_iter().rev().len(), expected.len());
                }

                #[test]
                fn in_order() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Doubly<_> = expected.iter().copied().collect();

                    assert!(actual.into_iter().rev().eq(expected.into_iter().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Doubly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.size_hint(), (expected.len(), Some(expected.len())));
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Doubly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.len(), expected.len());
                }

                #[test]
                fn updates() {
                    let mut actual = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                    let mut remaining = actual.len();

                    while let Some(_) = actual.next() {
                        remaining -= 1;

                        assert_eq!(actual.len(), remaining);
                    }
                }
            }

            mod fused {
                use super::*;

                #[test]
                fn empty() {
                    let mut actual = Doubly::<()>::default();

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }

                #[test]
                fn exhausted() {
                    let mut actual = Doubly::from_iter([()]);

                    // Exhaust the elements.
                    let _: () = actual.next().expect("the one element");

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }
            }
        }

        mod from {
            use super::*;

            #[test]
            fn empty() {
                let actual: Doubly<()> = core::iter::empty().collect();

                assert!(actual.head.is_none());
                assert!(actual.tail.is_none());
            }

            #[test]
            fn initializes_elements() {
                let expected = [0, 1, 2, 3, 4, 5];

                let actual: Doubly<_> = expected.iter().copied().collect();

                assert!(actual.eq(expected));
            }

            #[test]
            fn does_not_trust_size_hint() {
                let expected = [0, 1, 2, 3, 4, 5];

                // Ideally, this will panic if it uses the invalid size.
                let actual: Doubly<_> = (FaultySizeHintIter {
                    data: expected.iter().copied(),
                })
                .collect();

                assert_eq!(actual.len(), expected.len());
            }
        }

        mod extend {
            use super::*;

            #[test]
            #[allow(clippy::shadow_unrelated)]
            fn appends_elements() {
                let preexisting = [0, 1, 2];
                let mut actual: Doubly<_> = preexisting.into_iter().collect();

                let expected = [3, 4, 5];
                actual.extend(expected.iter().copied());

                for (actual, expected) in actual.skip(preexisting.len()).zip(expected) {
                    assert_eq!(actual, expected);
                }
            }

            #[test]
            fn does_not_modify_preexisting_elements() {
                let expected = [0, 1, 2];

                let mut actual: Doubly<_> = expected.into_iter().collect();

                actual.extend([3, 4, 5]);

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn into_empty_instance() {
                let mut actual = Doubly::<usize>::default();

                let expected = [0, 1, 2, 3, 4, 5];

                actual.extend(expected.iter().copied());

                assert!(actual.eq(expected));
            }

            #[test]
            fn from_empty_iterator() {
                let mut actual = Doubly::<()>::default();

                actual.extend(core::iter::empty());

                assert!(actual.head.is_none());
                assert!(actual.tail.is_none());
            }

            #[test]
            fn does_not_trust_size_hint() {
                let mut actual = Doubly::<usize>::default();

                let expected = [0, 1, 2, 3, 4, 5];

                // Ideally, this will panic if it uses the invalid size.
                actual.extend(FaultySizeHintIter {
                    data: expected.iter().copied(),
                });
            }
        }
    }

    mod collection {
        use super::*;

        mod count {
            use super::*;

            #[test]
            fn number_of_elements() {
                let actual = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                assert_eq!(Collection::count(&actual), 6);
            }
        }
    }

    mod linear {
        use super::*;

        mod iter {
            use super::*;

            #[test]
            fn element_count() {
                let expected = [0, 1, 2, 3, 4, 5];

                let actual: Doubly<_> = expected.iter().copied().collect();

                assert_eq!(actual.iter().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let expected = [0, 1, 2, 3, 4, 5];

                let actual: Doubly<_> = expected.iter().copied().collect();

                assert!(actual.iter().eq(expected.iter()));
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Doubly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.iter().rev().count(), expected.len());
                }

                #[test]
                fn in_order() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Doubly<_> = expected.iter().copied().collect();

                    assert!(actual.iter().rev().eq(expected.iter().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Doubly<_> = expected.iter().copied().collect();

                    assert_eq!(
                        actual.iter().size_hint(),
                        (expected.len(), Some(expected.len()))
                    );
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Doubly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.iter().len(), expected.len());
                }

                #[test]
                fn updates() {
                    let actual: Doubly<_> = [0, 1, 2, 3, 4, 5].iter().copied().collect();

                    let mut actual = actual.iter();

                    let mut remaining = actual.len();

                    while let Some(_) = actual.next() {
                        remaining -= 1;

                        assert_eq!(actual.len(), remaining);
                    }
                }
            }

            mod fused {
                use super::*;

                #[test]
                fn empty() {
                    let actual = Doubly::<()>::default();

                    let mut actual = actual.iter();

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }

                #[test]
                fn exhausted() {
                    let actual: Doubly<_> = [()].into_iter().collect();

                    let mut actual = actual.iter();

                    // Exhaust the elements.
                    let _: &() = actual.next().expect("the one element");

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }
            }
        }

        mod iter_mut {
            use super::*;

            #[test]
            fn element_count() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual: Doubly<_> = expected.iter().copied().collect();

                assert_eq!(actual.iter_mut().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let mut actual: Doubly<_> = expected.iter().copied().collect();

                assert!(actual.iter_mut().eq(expected.iter_mut()));
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let mut actual: Doubly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.iter_mut().rev().count(), expected.len());
                }

                #[test]
                fn in_order() {
                    let mut expected = [0, 1, 2, 3, 4, 5];

                    let mut actual: Doubly<_> = expected.iter().copied().collect();

                    assert!(actual.iter_mut().rev().eq(expected.iter_mut().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let mut actual: Doubly<_> = expected.iter().copied().collect();

                    assert_eq!(
                        actual.iter_mut().size_hint(),
                        (expected.len(), Some(expected.len()))
                    );
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let mut actual: Doubly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.iter_mut().len(), expected.len());
                }

                #[test]
                fn updates() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let mut actual: Doubly<_> = expected.iter().copied().collect();

                    let mut actual = actual.iter_mut();

                    let mut remaining = actual.len();

                    while let Some(_) = actual.next() {
                        remaining -= 1;

                        assert_eq!(actual.len(), remaining);
                    }
                }
            }

            mod fused {
                use super::*;

                #[test]
                fn empty() {
                    let mut actual = Doubly::<()>::default();

                    let mut actual = actual.iter_mut();

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }

                #[test]
                fn exhausted() {
                    let mut actual: Doubly<_> = [()].into_iter().collect();

                    let mut actual = actual.iter_mut();

                    // Exhaust the elements.
                    let _: &() = actual.next().expect("the one element");

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }
            }
        }

        mod at {
            use super::*;

            #[test]
            fn correct_element() {
                let expected = [0, 1, 2, 3, 4, 5];

                let actual: Doubly<_> = expected.iter().copied().collect();

                for (index, element) in expected.iter().enumerate() {
                    assert_eq!(actual.at(index), Some(element));
                }
            }

            #[test]
            fn none_when_index_out_of_bounds() {
                let actual = Doubly::<()>::default();

                assert!(actual.at(0).is_none());
            }
        }

        mod at_mut {
            use super::*;

            #[test]
            fn correct_element() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for (index, element) in expected.iter_mut().enumerate() {
                    assert_eq!(actual.at_mut(index), Some(element));
                }
            }

            #[test]
            fn is_mutable() {
                let mut actual: Doubly<_> = [0, 1, 2, 3, 4, 5].into_iter().collect();

                for index in 0..actual.len() {
                    let element = actual.at_mut(index).expect("within bounds");

                    *element = 12345;
                }

                for element in actual {
                    assert_eq!(element, 12345);
                }
            }

            #[test]
            fn none_when_index_out_of_bounds() {
                let mut actual = Doubly::<()>::default();

                assert!(actual.at_mut(0).is_none());
            }
        }

        mod first {
            use super::*;

            #[test]
            fn correct_element() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for element in expected {
                    assert_eq!(actual.first(), Some(&element));

                    _ = actual.next();
                }
            }

            #[test]
            fn none_when_empty() {
                let actual = Doubly::<()>::default();

                assert_eq!(actual.first(), None);
            }
        }

        mod last {
            use super::*;

            #[test]
            fn correct_element() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for element in expected.into_iter().rev() {
                    assert_eq!(Linear::last(&actual), Some(&element));

                    _ = actual.next_back();
                }
            }

            #[test]
            fn none_when_empty() {
                let actual = Doubly::<()>::default();

                assert_eq!(Linear::last(&actual), None);
            }
        }

        mod first_mut {
            use super::*;

            #[test]
            fn correct_element() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for mut element in expected {
                    assert_eq!(actual.first_mut(), Some(&mut element));

                    _ = actual.next();
                }
            }

            #[test]
            fn is_mutable() {
                let mut actual: Doubly<_> = [0, 1, 2, 3, 4, 5].into_iter().collect();

                let element = actual.first_mut().expect("the first element");

                *element = 12345;

                assert_eq!(actual.next(), Some(12345));
            }

            #[test]
            fn does_not_modify_other_elements() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual: Doubly<_> = expected.iter().copied().collect();

                _ = actual.first_mut().expect("the first element");

                assert!(actual.eq(expected));
            }

            #[test]
            fn none_when_empty() {
                let mut actual = Doubly::<()>::default();

                assert_eq!(actual.first_mut(), None);
            }
        }

        mod last_mut {
            use super::*;

            #[test]
            fn correct_element() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for mut element in expected.into_iter().rev() {
                    assert_eq!(actual.last_mut(), Some(&mut element));

                    _ = actual.next_back();
                }
            }

            #[test]
            fn is_mutable() {
                let mut actual: Doubly<_> = [0, 1, 2, 3, 4, 5].into_iter().collect();

                let element = actual.last_mut().expect("the first element");

                *element = 12345;

                assert_eq!(actual.next_back(), Some(12345));
            }

            #[test]
            fn does_not_modify_other_elements() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual: Doubly<_> = expected.iter().copied().collect();

                _ = actual.last_mut().expect("the first element");

                assert!(actual.eq(expected));
            }

            #[test]
            fn none_when_empty() {
                let mut actual = Doubly::<()>::default();

                assert_eq!(actual.last_mut(), None);
            }
        }
    }

    mod list {
        use super::*;

        mod insert {
            use super::*;

            #[test]
            fn adds_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                _ = actual.insert(2, 12345).expect("successful allocation");

                assert_eq!(actual.len(), expected.len() + 1);
            }

            #[test]
            fn initializes_element() {
                let mut actual: Doubly<_> = [0, 1, 2, 3, 4, 5].into_iter().collect();

                _ = actual.insert(2, 12345).expect("successful allocation");

                assert_eq!(actual[2], 12345);
            }

            #[test]
            fn yields_inserted_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                let actual = actual.insert(2, 12345).expect("successful allocation");

                assert_eq!(actual, &mut 12345);
            }

            #[test]
            fn does_not_modify_leading_elements() {
                const INDEX: usize = 2;

                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                _ = actual.insert(INDEX, 12345).expect("successful allocation");

                for index in 0..INDEX {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn does_not_modify_trailing_elements() {
                const INDEX: usize = 2;

                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                _ = actual.insert(INDEX, 12345).expect("successful allocation");

                for index in INDEX..expected.len() {
                    assert_eq!(actual[index + 1], expected[index]);
                }
            }

            #[test]
            fn when_empty() {
                let mut actual = Doubly::<usize>::default();

                assert!(actual.insert(0, 12345).is_ok());
                assert_eq!(actual.head, actual.tail);
                assert!(actual.eq([12345]));
            }

            #[test]
            fn can_prepend() {
                let mut actual: Doubly<_> = [0, 1, 2, 3, 4, 5].into_iter().collect();

                _ = actual.insert(0, 12345).expect("successful allocation");

                assert_eq!(actual[0], 12345);
            }

            #[test]
            fn can_append() {
                let mut actual: Doubly<_> = [0, 1, 2, 3, 4, 5].into_iter().collect();

                _ = actual.insert(6, 12345).expect("successful allocation");

                assert_eq!(actual[6], 12345);
            }
        }

        mod remove {
            use super::*;

            #[test]
            fn subtracts_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                _ = actual.remove(0).expect("valid index");

                assert_eq!(actual.len(), expected.len() - 1);
            }

            #[test]
            fn yields_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for element in expected {
                    let removed = actual.remove(0).expect("front element");

                    assert_eq!(removed, element);
                }
            }

            #[test]
            fn does_not_modify_leading_elements() {
                const INDEX: usize = 2;

                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                _ = actual.remove(INDEX).expect("valid index");

                for index in 0..INDEX {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn does_not_modify_trailing_elements() {
                const INDEX: usize = 2;

                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                _ = actual.remove(INDEX).expect("valid index");

                for index in INDEX..expected.len() - 1 {
                    assert_eq!(actual[index], expected[index + 1]);
                }
            }

            #[test]
            fn none_when_index_out_of_bounds() {
                let mut actual = Doubly::<()>::default();

                assert!(actual.remove(0).is_none());
            }
        }

        mod prepend {
            use super::*;

            #[test]
            fn adds_element() {
                let expected = [1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                _ = actual.prepend(0).expect("successful allocation");

                assert_eq!(actual.len(), expected.len() + 1);
            }

            #[test]
            fn initializes_element() {
                let mut actual: Doubly<_> = [1, 2, 3, 4, 5].into_iter().collect();

                _ = actual.prepend(0).expect("successful allocation");

                assert_eq!(actual[0], 0);
            }

            #[test]
            fn yields_inserted_element() {
                let expected = [1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                let actual = actual.prepend(0).expect("successful allocation");

                assert_eq!(actual, &mut 0);
            }

            #[test]
            fn does_not_modify_trailing_elements() {
                let expected = [1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                _ = actual.prepend(0).expect("successful allocation");

                for index in 0..expected.len() {
                    assert_eq!(actual[index + 1], expected[index]);
                }
            }

            #[test]
            fn when_empty() {
                let mut actual = Doubly::<usize>::default();

                assert!(actual.prepend(0).is_ok());
                assert_eq!(actual.head, actual.tail);
                assert!(actual.eq([0]));
            }
        }

        mod append {
            use super::*;

            #[test]
            fn adds_element() {
                let expected = [0, 1, 2, 3, 4];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                _ = actual.append(5).expect("successful allocation");

                assert_eq!(actual.len(), expected.len() + 1);
            }

            #[test]
            fn initializes_element() {
                let mut actual: Doubly<_> = [0, 1, 2, 3, 4].into_iter().collect();

                _ = actual.append(5).expect("successful allocation");

                assert_eq!(actual[5], 5);
            }

            #[test]
            fn yields_inserted_element() {
                let expected = [0, 1, 2, 3, 4];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                let actual = actual.append(5).expect("successful allocation");

                assert_eq!(actual, &mut 5);
            }

            #[test]
            fn does_not_modify_leading_elements() {
                let expected = [0, 1, 2, 3, 4];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                _ = actual.append(5).expect("successful allocation");

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn when_empty() {
                let mut actual = Doubly::<usize>::default();

                assert!(actual.append(0).is_ok());
                assert_eq!(actual.head, actual.tail);
                assert!(actual.eq([0]));
            }
        }

        mod front {
            use super::*;

            #[test]
            fn subtracts_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for remaining in (0..expected.len()).rev() {
                    _ = actual.front();

                    assert_eq!(actual.len(), remaining);
                }
            }

            #[test]
            fn does_not_modify_trailing_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for offset in 1..=expected.len() {
                    _ = actual.front();

                    assert!(actual.iter().eq(expected[offset..].iter()));
                }

                assert_eq!(actual.head, None);
                assert_eq!(actual.tail, None);
            }

            #[test]
            fn yields_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for element in expected {
                    assert_eq!(actual.front(), Some(element));
                }
            }

            #[test]
            fn none_when_empty() {
                let mut actual = Doubly::<()>::default();

                assert_eq!(actual.front(), None);
            }
        }

        mod back {
            use super::*;

            #[test]
            fn subtracts_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for remaining in (0..expected.len()).rev() {
                    _ = actual.back();

                    assert_eq!(actual.len(), remaining);
                }
            }

            #[test]
            fn does_not_modify_leading_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for offset in (0..expected.len()).rev() {
                    _ = actual.back();

                    assert!(actual.iter().eq(expected[..offset].iter()));
                }

                assert_eq!(actual.head, None);
                assert_eq!(actual.tail, None);
            }

            #[test]
            fn yields_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for element in expected.into_iter().rev() {
                    assert_eq!(actual.back(), Some(element));
                }
            }

            #[test]
            fn none_when_empty() {
                let mut actual = Doubly::<()>::default();

                assert_eq!(actual.back(), None);
            }
        }

        mod drain {
            use super::*;

            #[test]
            fn none_when_out_of_bounds_range() {
                let mut instance = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                let mut actual = instance.drain(256..);

                assert_eq!(actual.next(), None);
                assert_eq!(actual.next_back(), None);

                drop(actual);
            }

            mod iterator {
                use super::*;

                #[test]
                fn element_count() {
                    let mut expected = vec![0, 1, 2, 3, 4, 5];
                    let mut actual: Doubly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.drain(1..4).count(), expected.drain(1..4).count());
                }

                #[test]
                fn in_order() {
                    let mut expected = vec![0, 1, 2, 3, 4, 5];
                    let mut actual: Doubly<_> = expected.iter().copied().collect();

                    assert!(actual.drain(1..4).eq(expected.drain(1..4)));
                }

                mod double_ended {
                    use super::*;

                    #[test]
                    fn element_count() {
                        let mut expected = vec![0, 1, 2, 3, 4, 5];
                        let mut actual: Doubly<_> = expected.iter().copied().collect();

                        assert_eq!(
                            actual.drain(1..4).rev().count(),
                            expected.drain(1..4).rev().count()
                        );
                    }

                    #[test]
                    fn in_order() {
                        let mut expected = vec![0, 1, 2, 3, 4, 5];
                        let mut actual: Doubly<_> = expected.iter().copied().collect();

                        assert!(actual.drain(1..4).rev().eq(expected.drain(1..4).rev()));
                    }
                }

                mod exact_size {
                    use super::*;

                    #[test]
                    fn hint() {
                        let mut expected = vec![0, 1, 2, 3, 4, 5];
                        let mut actual: Doubly<_> = expected.iter().copied().collect();

                        let expected = expected.drain(1..4);

                        assert_eq!(
                            actual.drain(1..4).size_hint(),
                            (expected.len(), Some(expected.len()))
                        );
                    }

                    #[test]
                    fn len() {
                        let mut expected = vec![0, 1, 2, 3, 4, 5];
                        let mut actual: Doubly<_> = expected.iter().copied().collect();

                        assert_eq!(actual.drain(1..4).len(), expected.drain(1..4).len());
                    }
                }

                mod fused {
                    use super::*;

                    #[test]
                    fn empty() {
                        let mut actual = Doubly::<()>::default();
                        let mut actual = actual.drain(0..=0);

                        // Yields `None` at least once.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);

                        // Continues to yield `None`.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }

                    #[test]
                    fn exhausted() {
                        let mut actual: Doubly<_> = [()].into_iter().collect();
                        let mut actual = actual.drain(0..=0);

                        // Exhaust the elements.
                        let _: () = actual.next().expect("the one element");

                        // Yields `None` at least once.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);

                        // Continues to yield `None`.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }
                }
            }

            mod drop {
                use super::*;

                #[test]
                fn removes_yielded_elements() {
                    let mut actual = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(..));

                    assert!(actual.head.is_none());
                    assert!(actual.tail.is_none());

                    assert_eq!(actual.len(), 0);
                }

                #[test]
                fn does_not_modify_leading_elements() {
                    let mut actual = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(3..));

                    assert!(actual.eq([0, 1, 2]));
                }

                #[test]
                fn does_not_modify_trailing_elements() {
                    let mut actual = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(..3));

                    assert!(actual.eq([3, 4, 5]));
                }

                #[test]
                fn combines_leading_and_trailing_elements() {
                    let mut actual = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(1..=4));

                    assert!(actual.eq([0, 5]));
                }
            }
        }

        mod withdraw {
            use super::*;

            mod iterator {
                use super::*;

                #[test]
                fn element_count() {
                    let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                    let actual = underlying.withdraw(|element| element % 2 == 0);

                    assert_eq!(actual.count(), 3);
                }

                #[test]
                fn in_order() {
                    let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                    let actual = underlying.withdraw(|element| element % 2 == 0);

                    assert!(actual.eq([0, 2, 4]));
                }

                #[test]
                fn combines_retained_elements() {
                    let mut actual = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.withdraw(|element| element == &1));

                    assert!(actual.eq([0, 2, 3, 4, 5]));
                }

                #[test]
                fn size_hint() {
                    let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                    let mut actual = underlying.withdraw(|element| element % 2 == 0);

                    assert_eq!(actual.size_hint(), (0, Some(6)));

                    _ = actual.next().expect("element with value 0");
                    assert_eq!(actual.size_hint(), (0, Some(5)));

                    _ = actual.next().expect("element with value 2");
                    assert_eq!(actual.size_hint(), (0, Some(3)));

                    _ = actual.next().expect("element with value 4");
                    assert_eq!(actual.size_hint(), (0, Some(1)));

                    _ = actual.next();
                    assert_eq!(actual.size_hint(), (0, Some(0)));
                }

                mod double_ended {
                    use super::*;

                    #[test]
                    fn element_count() {
                        let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                        let actual = underlying.withdraw(|element| element % 2 == 0).rev();

                        assert_eq!(actual.count(), 3);
                    }

                    #[test]
                    fn in_order() {
                        let mut underlying = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                        let actual = underlying.withdraw(|element| element % 2 == 0).rev();

                        assert!(actual.eq([4, 2, 0]));
                    }

                    #[test]
                    fn combines_retained_elements() {
                        let mut actual = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                        drop(actual.withdraw(|element| element == &1).rev());

                        assert!(actual.eq([0, 2, 3, 4, 5]));
                    }

                    #[test]
                    fn prevents_elements_from_being_yielded_more_than_once() {
                        let mut underlying = Doubly::from_iter([0, 1, 2, 0]);

                        let mut actual = underlying.withdraw(|element| element != &0);

                        // make head and tail meet.
                        _ = actual.next().expect("the element with value '1'");
                        _ = actual.next_back().expect("the element with value '2'");

                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }
                }

                mod fused {
                    use super::*;

                    #[test]
                    fn empty() {
                        let mut underlying = Doubly::from_iter([0]);
                        let mut actual = underlying.withdraw(|element| element % 2 == 0);

                        // Exhaust the elements.
                        _ = actual.next().expect("the one element");

                        // Yields `None` at least once.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);

                        // Continues to yield `None`.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }

                    #[test]
                    fn exhausted() {
                        let mut underlying = Doubly::<usize>::default();
                        let mut actual = underlying.withdraw(|element| element % 2 == 0);

                        // Yields `None` at least once.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);

                        // Continues to yield `None`.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }
                }
            }

            mod drop {
                use super::*;

                #[test]
                fn drops_yet_to_be_yielded_elements() {
                    let mut actual = Doubly::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.withdraw(|element| element % 2 == 0));

                    assert!(actual.eq([1, 3, 5]));
                }
            }
        }
    }

    mod stack {
        use super::*;

        mod push {
            use super::*;

            #[test]
            fn adds_element() {
                let expected = [1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                _ = actual.push(0).expect("successful allocation");

                assert_eq!(actual.len(), expected.len() + 1);
            }

            #[test]
            fn initializes_element() {
                let mut actual: Doubly<_> = [1, 2, 3, 4, 5].into_iter().collect();

                _ = actual.push(0).expect("successful allocation");

                assert_eq!(actual[0], 0);
            }

            #[test]
            fn yields_inserted_element() {
                let expected = [1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                let actual = actual.push(0).expect("successful allocation");

                assert_eq!(actual, &mut 0);
            }

            #[test]
            fn does_not_modify_trailing_elements() {
                let expected = [1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                _ = actual.push(0).expect("successful allocation");

                for index in 0..expected.len() {
                    assert_eq!(actual[index + 1], expected[index]);
                }
            }

            #[test]
            fn when_empty() {
                let mut actual = Doubly::<usize>::default();

                assert!(actual.push(0).is_ok());
                assert!(actual.eq([0]));
            }
        }

        mod pop {
            use super::*;

            #[test]
            fn subtracts_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for remaining in (0..expected.len()).rev() {
                    _ = actual.pop();

                    assert_eq!(actual.len(), remaining);
                }
            }

            #[test]
            fn does_not_modify_trailing_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for offset in 1..=expected.len() {
                    _ = actual.pop();

                    assert!(actual.iter().eq(expected[offset..].iter()));
                }

                assert!(actual.head.is_none());
                assert!(actual.tail.is_none());
            }

            #[test]
            fn yields_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for element in expected {
                    assert_eq!(actual.pop(), Some(element));
                }
            }

            #[test]
            fn none_when_empty() {
                let mut actual = Doubly::<()>::default();

                assert_eq!(actual.pop(), None);
            }
        }

        mod peek {
            use super::*;

            #[test]
            fn correct_element() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual: Doubly<_> = expected.iter().copied().collect();

                for element in expected {
                    assert_eq!(actual.peek(), Some(&element));

                    _ = actual.pop();
                }
            }

            #[test]
            fn none_when_empty() {
                let actual = Doubly::<()>::default();

                assert_eq!(actual.peek(), None);
            }
        }
    }
}
