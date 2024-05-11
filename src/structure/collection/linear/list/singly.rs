//! Implementation of [`Singly`].

use super::Collection;
use super::Linear;
use super::List;

// TODO(oddnerd): examples for everything

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

impl<T> Drop for Singly<T> {
    /// Iteratively drop all contained elements.
    ///
    /// The default destructor implementation will _NOT_ be tail recursive,
    /// this means it will not optimize to an iterative implementation, hence
    /// it could overflow the call stack if enough elements are contained.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let instance = Singly::<()>::default();
    ///
    /// for _ in 0..usize::MAX {
    ///     instance.prepend(());
    /// }
    ///
    /// core::mem::drop(instance);
    /// ```
    fn drop(&mut self) {
        let mut next = self.elements.take();

        while let Some(mut current) = next {
            next = current.next.take();

            drop(current);
        }
    }
}

impl<T> Default for Singly<T> {
    /// Create an empty instance of [`Singly`].
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let instance = Singly::<usize>::default();
    ///
    /// assert_eq!(instance.len(), 0);
    /// ```
    fn default() -> Self {
        Singly { elements: None }
    }
}

impl<T: core::fmt::Debug> core::fmt::Debug for Singly<T> {
    /// List the elements contained.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Singly::from_iter(expected.iter().copied());
    ///
    /// assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    /// ```
    fn fmt(&self, output: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        output.debug_list().entries(self.iter()).finish()
    }
}

impl<T> core::ops::Index<usize> for Singly<T> {
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
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Singly::from_iter(expected.iter().copied());
    ///
    /// for index in 0..expected.len() {
    ///     use core::ops::Index;
    ///     assert_eq!(actual.index(index), expected.index(index));
    /// }
    /// ```
    fn index(&self, index: usize) -> &Self::Output {
        let mut next = self.elements.as_deref();

        for _ in 0..index {
            if let Some(current) = next {
                next = current.next.as_deref();
            } else {
                break;
            }
        }

        next.map_or_else(|| panic!("index out of bounds"), |node| &node.element)
    }
}

impl<T> core::ops::IndexMut<usize> for Singly<T> {
    /// Obtain a mutable reference to the element at position `index`.
    ///
    /// # Panics
    /// This method has the precondition that `index` is within bounds.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Singly::from_iter(expected.iter().copied());
    ///
    /// for index in 0..expected.len() {
    ///     use core::ops::IndexMut;
    ///     assert_eq!(actual.index_mut(index), expected.index_mut(index));
    /// }
    /// ```
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        let mut next = self.elements.as_deref_mut();

        for _ in 0..index {
            if let Some(current) = next {
                next = current.next.as_deref_mut();
            } else {
                break;
            }
        }

        next.map_or_else(|| panic!("index out of bounds"), |node| &mut node.element)
    }
}

impl<T> Iterator for Singly<T> {
    type Item = T;

    /// Obtain the first element by value via moving it out of [`Self`].
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let instance = Singly::from_iter([0, 1, 2, 3, 4, 5]).into_iter();
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
        self.front()
    }

    /// Query how many elements are contained.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let instance = Singly::from_iter([0, 1, 2, 3, 4, 5]).into_iter();
    ///
    /// assert_eq!(instance.size_hint(), (6, Some(6)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        let count = self.count();

        (count, Some(count))
    }
}

impl<T> DoubleEndedIterator for Singly<T> {
    /// Obtain the last element by value via moving it out of [`Self`].
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let instance = Singly::from_iter([0, 1, 2, 3, 4, 5]).into_iter();
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
        self.back()
    }
}

impl<T> ExactSizeIterator for Singly<T> {}

impl<T> core::iter::FusedIterator for Singly<T> {}

impl<T> Extend<T> for Singly<T> {
    /// Append the elements in `iter` maintaining order.
    ///
    /// Using [`Self::append`] directly would be O(N^2) since it is required to
    /// traverse all existing elements for each insertion whereas this method
    /// maintains a pointer to the last element thereby being more efficient.
    ///
    /// # Panics
    /// The Rust runtime might abort if allocation fails, panics otherwise.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let instance = Singly::from_iter([0, 1, 2]);
    ///
    /// instance.extend([3, 4, 5]);
    ///
    /// assert!(instance.iter().eq([0, 1, 2, 3, 4, 5]));
    /// ```
    fn extend<Iter: IntoIterator<Item = T>>(&mut self, iter: Iter) {
        let mut current = &mut self.elements;

        while let &mut Some(ref mut next) = current {
            current = &mut next.next;
        }

        for element in iter {
            let element = Box::new(Node{element, next: None});

            current = &mut current.insert(element).next;
        }
    }
}

impl<T> FromIterator<T> for Singly<T> {
    /// Construct an instance with elements from an iterator.
    ///
    /// # Panics
    /// The Rust runtime might abort if allocation fails, panics otherwise.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(N) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Singly::from_iter(expected.iter().copied());
    ///
    /// assert!(actual.iter().eq(expected));
    /// ```
    fn from_iter<Iter: IntoIterator<Item = T>>(iter: Iter) -> Self {
        let mut instance = Singly::<T>::default();

        instance.extend(iter);

        instance
    }
}

impl<'a, T: 'a> Collection for Singly<T> {
    type Element = T;

    /// Query how many elements are contained.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::Collection;
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let instance = Singly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(instance.count(), 6);
    /// ```
    #[allow(clippy::ref_patterns)]
    #[allow(clippy::needless_borrowed_reference)]
    fn count(&self) -> usize {
        let mut count: usize = 0;

        let mut next = &self.elements;

        while let &Some(ref current) = next {
            if let Some(incremented) = count.checked_add(1) {
                count = incremented;
            } else {
                unreachable!("more than usize::MAX elements");
            }

            next = &current.next;
        }

        count
    }
}

impl<T> Linear for Singly<T> {
    /// Iterate over the elements by immutable reference.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let instance = Singly::from_iter(expected.iter().copied());
    ///
    /// assert!(instance.iter().eq(expected.iter()));
    /// ```
    fn iter(
        &self,
    ) -> impl DoubleEndedIterator<Item = &Self::Element> + ExactSizeIterator + core::iter::FusedIterator
    {
        Iter {
            next: self.elements.as_deref(),
            previous_back: None,
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
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    /// let mut instance = Singly::from_iter(expected.iter().copied());
    ///
    /// assert!(instance.iter_mut().eq(expected.iter_mut()));
    /// ```
    fn iter_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = &mut Self::Element>
           + ExactSizeIterator
           + core::iter::FusedIterator {
        IterMut {
            next: self.elements.as_deref_mut(),
            previous_back: None,
        }
    }
}

impl<T> List for Singly<T> {
    /// Move an `element` into a new node at `index`.
    ///
    /// # Panics
    /// The Rust runtime might abort if allocation fails, panics otherwise.
    ///
    /// # Performance
    /// This method takes O(N) times and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::List;
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let instance = Singly::from_iter([0, 1, 2, 4, 5]);
    ///
    /// assert!(instance.insert(3, 3).is_ok_and(|inserted| inserted = &mut 3))
    /// assert!(instance.iter().eq([0, 1, 2, 3, 4, 5]);
    /// ```
    fn insert(
        &mut self,
        index: usize,
        element: Self::Element,
    ) -> Result<&mut Self::Element, Self::Element> {
        let new = Box::new(Node {
            element,
            next: None,
        });

        if self.elements.is_none() && index == 0 {
            let new = self.elements.insert(new);
            return Ok(&mut new.element);
        }

        let mut current = self.elements.as_deref_mut();

        for _ in 0..index {
            current = current.and_then(|current| current.next.as_deref_mut());
        }

        if let Some(preceding) = current {
            let succeeding = preceding.next.take();
            let new = preceding.next.insert(new);
            new.next = succeeding;

            Ok(&mut new.element)
        } else {
            Err(new.element)
        }
    }

    /// Move the element at `index` out, if it exists.
    ///
    /// # Performance
    /// This method takes O(N) times and consumes O(1) memory.
    fn remove(&mut self, index: usize) -> Option<Self::Element> {
        if index == 0 {
            let node = self.elements.take()?;
            self.elements = node.next;
            return Some(node.element);
        }

        let mut current = self.elements.as_deref_mut();

        for _ in 0..index - 1 {
            current = current.and_then(|current| current.next.as_deref_mut());
        }

        if let Some(preceding) = current {
            let mut node = preceding.next.take()?;
            let succeeding = node.next.take();
            preceding.next = succeeding;

            Some(node.element)
        } else {
            unreachable!("at least two elements");
        }
    }

    /// Efficiently remove the elements within the given index `range`.
    ///
    /// Using [`Self::remove`] would be inefficient because each removal would
    /// require traversing the list to the given index which is O(N^2) time,
    /// whereas this method traverses the list only once there being O(N).
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn drain(
        &mut self,
        range: impl core::ops::RangeBounds<usize>,
    ) -> impl DoubleEndedIterator<Item = Self::Element> + ExactSizeIterator {
        let start = match range.start_bound() {
            core::ops::Bound::Included(start) => *start,
            core::ops::Bound::Excluded(start) => match start.checked_add(1) {
                Some(start) => start,
                None => {
                    // TODO: does this special case drop?
                    return Drain {
                        underlying: Some(self),
                        preceding: None,
                        next: None,
                        remaining: 0,
                    };
                }
            },
            core::ops::Bound::Unbounded => 0,
        };

        let remaining = match range.end_bound() {
            core::ops::Bound::Included(end) => (end - start).saturating_add(1),
            core::ops::Bound::Excluded(end) => end - start,
            core::ops::Bound::Unbounded => self.len() - start,
        };

        if start == 0 {
            let next = self.elements.take();

            return Drain {
                underlying: Some(self),
                preceding: None,
                next,
                remaining,
            };
        }

        let mut current = self.elements.as_deref_mut();

        for _ in 0..start {
            current = current.and_then(|current| current.next.as_deref_mut());
        }

        if let Some(preceding) = current {
            let next = preceding.next.take();

            Drain {
                underlying: None,
                preceding: Some(preceding),
                next,
                remaining,
            }
        } else {
            unreachable!("preceding elements");
        }
    }

    fn withdraw(
        &mut self,
        predicate: impl FnMut(&Self::Element) -> bool,
    ) -> impl DoubleEndedIterator<Item = Self::Element> {
        let next = self.elements.take();

        Withdraw {
            underlying: Some(self),
            preceding: None,
            next,
            previous_back: None,
            predicate,
        }
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
                unreachable!("more than `usize::MAX` elements");
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
                unreachable!("more than `usize::MAX` elements");
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

/// By-value iterator over a range of indices.
struct Drain<'a, T> {
    /// The underlying elements being drained from.
    underlying: Option<&'a mut Singly<T>>,

    /// The node preceding those being drained, if any.
    preceding: Option<&'a mut Node<T>>,

    /// The remaining elements of the list, if any.
    next: Option<Box<Node<T>>>,

    /// The number of elements yet to be yielded.
    remaining: usize,
}

impl<'a, T: 'a> Drop for Drain<'a, T> {
    /// Remove elements yet to be drained and repair the underlying [`Singly`].
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn drop(&mut self) {
        self.for_each(drop);

        if let Some(preceding) = self.preceding.take() {
            preceding.next = self.next.take();
        } else {
            let Some(underlying) = self.underlying.take() else {
                unreachable!("constructor logic error");
            };

            underlying.elements = self.next.take();
        }
    }
}

impl<'a, T: 'a> Iterator for Drain<'a, T> {
    type Item = T;

    /// Obtain the next element from the front, if any exists.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    fn next(&mut self) -> Option<Self::Item> {
        let mut current = self.next.take()?;

        self.next = current.next.take();

        self.remaining -= 1;

        Some(current.element)
    }

    /// Query how many elements have yet to be yielded.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn size_hint(&self) -> (usize, Option<usize>) {
        let mut current = &self.next;

        for count in 0..self.remaining {
            let Some(node) = current else {
                return (count, Some(count));
            };

            current = &node.next;
        }

        (self.remaining, Some(self.remaining))
    }
}

impl<'a, T: 'a> DoubleEndedIterator for Drain<'a, T> {
    /// Obtain the next element from the back, if any exists.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn next_back(&mut self) -> Option<Self::Item> {
        let mut current = self.next.as_deref_mut();

        for _ in 0..self.remaining - 1 {
            current = current.and_then(|current| current.next.as_deref_mut());
        }

        if let Some(preceding) = current {
            let mut node = preceding.next.take()?;
            let succeeding = node.next.take();
            preceding.next = succeeding;

            self.remaining -= 1;

            Some(node.element)
        } else {
            None
        }
    }
}

impl<'a, T: 'a> ExactSizeIterator for Drain<'a, T> {}

impl<'a, T: 'a> core::iter::FusedIterator for Drain<'a, T> {}

/// By-value iterator over values which match some predicate.
struct Withdraw<'a, T, F: FnMut(&T) -> bool> {
    /// The underlying elements being drained from.
    underlying: Option<&'a mut Singly<T>>,

    /// The node preceding those being drained, if any.
    preceding: Option<&'a mut Node<T>>,

    /// The remaining elements of the list, if any.
    next: Option<Box<Node<T>>>,

    /// The previously yielded element from the back, if any.
    previous_back: Option<*const Node<T>>,

    /// The predicate based upon which elements are withdrawn.
    predicate: F,
}

impl<T, F: FnMut(&T) -> bool> Drop for Withdraw<'_, T, F> {
    /// Drop elements yet to be yielded and repair the underlying [`Singly`].
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn drop(&mut self) {
        self.for_each(drop);

        if let Some(preceding) = self.preceding.take() {
            preceding.next = self.next.take();
        } else if let Some(underlying) = self.underlying.take() {
            underlying.elements = self.next.take();
        } else {
            unreachable!("logic error");
        }
    }
}

impl<T, F: FnMut(&T) -> bool> Iterator for Withdraw<'_, T, F> {
    type Item = T;

    /// Obtain the next elements matching the predicate, if any.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn next(&mut self) -> Option<Self::Item> {
        while let Some(mut current) = self.next.take() {
            if let Some(sentinel) = self.previous_back {
                if core::ptr::addr_eq(current.as_ref(), sentinel) {
                    break;
                }
            }

            if (self.predicate)(&current.element) {
                if let Some(preceding) = self.preceding.take() {
                    preceding.next = current.next;
                } else if let Some(underlying) = self.underlying.take() {
                    underlying.elements = current.next;
                } else {
                    unreachable!("logic error");
                }

                return Some(current.element);
            }

            self.next = current.next.take();

            if let Some(preceding) = self.preceding.take() {
                let current = preceding.next.insert(current);
                self.preceding = Some(current);
            } else if let Some(underlying) = self.underlying.take() {
                let current = underlying.elements.insert(current);
                self.preceding = Some(current);
            } else {
                unreachable!("logic error");
            }
        }

        None
    }

    /// Query how many elements could be yielded.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn size_hint(&self) -> (usize, Option<usize>) {
        let Some(mut current) = self.next.as_deref() else {
            return (0, Some(0));
        };

        let mut remaining: usize = 1;

        while let Some(next) = current.next.as_deref() {
            current = next;
            remaining += 1;
        }

        (0, Some(remaining))
    }
}

impl<T, F: FnMut(&T) -> bool> DoubleEndedIterator for Withdraw<'_, T, F> {
    /// Obtain the last element matching the predicate, if any.
    ///
    /// # Performance
    /// This method takes O(N^2) time and consumes O(1) memory.
    #[allow(clippy::redundant_else)]
    fn next_back(&mut self) -> Option<Self::Item> {
        // TODO(oddnerd): this is the worst code I have ever written.

        while self.next.is_some() {
            if let Some(mut first) = self.next.take() {
                if let Some(second) = first.next.take() {
                    if second.next.is_none() {
                        if (self.predicate)(&second.element) {
                            self.next = Some(first);
                            return Some(second.element);
                        } else if (self.predicate)(&first.element) {
                            if let Some(underlying) = self.underlying.take() {
                                underlying.elements = Some(second);
                            } else if let Some(preceding) = self.preceding.take() {
                                preceding.next = Some(second);
                            } else {
                                unreachable!("logic error");
                            }

                            return Some(first.element);
                        } else {
                            first.next = Some(second);

                            if let Some(underlying) = self.underlying.take() {
                                underlying.elements = Some(first);
                            } else if let Some(preceding) = self.preceding.take() {
                                preceding.next = Some(first);
                            } else {
                                unreachable!("logic error");
                            }
                        }
                    } else {
                        first.next = Some(second);
                        self.next = Some(first);
                        // handle with below loop
                    }
                } else if (self.predicate)(&first.element) {
                    return Some(first.element);
                } else {
                    if let Some(underlying) = self.underlying.take() {
                        underlying.elements = Some(first);
                    } else if let Some(preceding) = self.preceding.take() {
                        preceding.next = Some(first);
                    } else {
                        unreachable!("logic error");
                    }

                    return None;
                }
            }

            let mut current = self.next.as_deref_mut();

            while let Some(next) = current.take() {
                if let Some(next_next) = next.next.as_deref_mut() {
                    if let Some(next_next_next) = next_next.next.as_deref_mut() {
                        if let Some(sentinel) = self.previous_back {
                            if core::ptr::addr_eq(next_next_next, sentinel) {
                                // current (second last) -> last -> sentinel
                                break;
                            }
                        }
                    } else {
                        unreachable!("only two elements");
                    }

                    current = Some(next);
                } else {
                    unreachable!("only one element");
                }
            }

            let Some(second_last) = current else {
                unreachable!("no next element");
            };

            let Some(last) = second_last.next.as_deref_mut() else {
                unreachable!("was actually last element");
            };

            if (self.predicate)(&last.element) {
                let Some(popped) = second_last.next.take() else {
                    unreachable!("was actually last element");
                };

                second_last.next = popped.next;
                return Some(popped.element);
            } else {
                self.previous_back = Some(last);
            }
        }

        None
    }
}

impl<T, F: FnMut(&T) -> bool> ExactSizeIterator for Withdraw<'_, T, F> {}

impl<T, F: FnMut(&T) -> bool> core::iter::FusedIterator for Withdraw<'_, T, F> {}
