//! Implementation of [`Singly`].

use super::Collection;
use super::Linear;
use super::List;

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
    /// drop(instance);
    /// ```
    fn drop(&mut self) {
        for element in self {
            drop(element);
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

impl<T: Clone> Clone for Singly<T> {
    /// Clone all contained elements into a new instance of [`Singly`].
    ///
    /// # Panics
    /// The Rust runtime might abort if allocation fails, panics otherwise.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(N) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let original = Singly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// let clone = original.clone();
    ///
    /// assert_eq!(clone, original);
    /// ```
    fn clone(&self) -> Self {
        self.iter().cloned().collect()
    }
}

impl<T: PartialEq> PartialEq for Singly<T> {
    /// Query if `other` has the same elements in the same order.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let elements = [0, 1, 2, 3, 4, 5];
    ///
    /// let original = Singly::from_iter(elements.iter().copied());
    /// let other = Singly::from_iter(elements.iter().copied());
    ///
    /// assert_eq!(clone, original);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T: Eq> Eq for Singly<T> {}

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
        let removed = self.elements.take()?;

        self.elements = removed.next;

        Some(removed.element)
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
        let mut removed = self.elements.take()?;
        let mut successor = removed.next.take();
        let mut predecessor = &mut self.elements;

        while let Some(mut current) = successor.take() {
            successor = current.next.take();
            predecessor = &mut predecessor.insert(removed).next;
            removed = current;
        }

        Some(removed.element)
    }
}

impl<T> ExactSizeIterator for Singly<T> {}

impl<T> core::iter::FusedIterator for Singly<T> {}

impl<T> Extend<T> for Singly<T> {
    /// Append the `elements` at the end, maintaining order.
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
    fn extend<Iter: IntoIterator<Item = T>>(&mut self, elements: Iter) {
        let mut current = &mut self.elements;

        while let &mut Some(ref mut next) = current {
            current = &mut next.next;
        }

        for element in elements {
            let element = Box::new(Node {
                element,
                next: None,
            });

            current = &mut current.insert(element).next;
        }
    }
}

impl<T> FromIterator<T> for Singly<T> {
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
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Singly::from_iter(expected.iter().copied());
    ///
    /// assert!(actual.iter().eq(expected));
    /// ```
    fn from_iter<Iter: IntoIterator<Item = T>>(elements: Iter) -> Self {
        let mut instance = Singly::<T>::default();

        instance.extend(elements);

        instance
    }
}

impl<T> Collection for Singly<T> {
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
    fn count(&self) -> usize {
        let mut count: usize = 0;

        let mut next = &self.elements;

        while let Some(current) = next.as_deref() {
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
            next: &self.elements,
            previous_back: core::ptr::null(),
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
            previous_back: core::ptr::null(),
        }
    }
}

impl<T> List for Singly<T> {
    /// Move an `element` into such that it becomes the element at `index`.
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
    /// assert!(instance.insert(3, 3).is_ok_and(|inserted| inserted == &mut 3))
    /// assert!(instance.iter().eq([0, 1, 2, 3, 4, 5]);
    /// ```
    fn insert(
        &mut self,
        index: usize,
        element: Self::Element,
    ) -> Result<&mut Self::Element, Self::Element> {
        let mut next = &mut self.elements;

        for _ in 0..index {
            if let &mut Some(ref mut current) = next {
                next = &mut current.next;
            } else {
                return Err(element);
            }
        }

        let new = Box::new(Node {
            element,
            next: next.take(),
        });

        Ok(&mut next.insert(new).element)
    }

    /// Move the element at `index` out, if it exists.
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
    /// let instance = Singly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert!(instance.remove(3).is_ok_and(|inserted| inserted == 3))
    /// assert!(instance.iter().eq([0, 1, 2, 4, 5]);
    /// ```
    fn remove(&mut self, index: usize) -> Option<Self::Element> {
        let mut next = &mut self.elements;

        for _ in 0..index {
            if let &mut Some(ref mut current) = next {
                next = &mut current.next;
            } else {
                return None;
            }
        }

        next.take().map(|removed| {
            *next = removed.next;

            removed.element
        })
    }

    /// Efficiently remove the elements within the given index `range`.
    ///
    /// Using [`Self::remove`] would be inefficient because each removal would
    /// require traversing the list to the given index which is O(N^2) time,
    /// whereas this method traverses the list only once thereby being O(N).
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    fn drain(
        &mut self,
        range: impl core::ops::RangeBounds<usize>,
    ) -> impl DoubleEndedIterator<Item = Self::Element> + ExactSizeIterator {
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

        let mut next = &mut self.elements;

        for _ in 0..offset {
            if let &mut Some(ref mut current) = next {
                next = &mut current.next;
            } else {
                break;
            }
        }

        Drain { next, remaining }
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
    next: &'a Option<Box<Node<T>>>,

    /// The previously yielded element from the back, if any.
    previous_back: *const Node<T>,
}

impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;

    /// Obtain the next element from the front, if any.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let mut underlying = Singly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut instance = underlying.iter_mut();
    ///
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&3));
    /// assert_eq!(iter.next(), Some(&4));
    /// assert_eq!(iter.next(), Some(&5));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        self.next.as_deref().and_then(|current| {
            if core::ptr::addr_eq(current, self.previous_back) {
                None
            } else {
                self.next = &current.next;
                Some(&current.element)
            }
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
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let instance = Singly::from_iter([0, 1, 2, 4, 4, 5]).iter();
    ///
    /// assert_eq!(instance.iter().size_hint(), (6, Some(6)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        let mut count: usize = 0;

        let mut next = self.next;

        while let Some(current) = next.as_deref() {
            if let Some(incremented) = count.checked_add(1) {
                count = incremented;
            } else {
                unreachable!("more than usize::MAX elements");
            }

            next = &current.next;
        }

        (count, Some(count))
    }
}

impl<'a, T: 'a> DoubleEndedIterator for Iter<'a, T> {
    /// Obtain the next element from the back, if any.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let underlying = Singly::from_iter([0, 1, 2, 4, 5]);
    /// let instance = underlying.iter().rev();
    ///
    /// assert_eq!(iter.next(), Some(&5));
    /// assert_eq!(iter.next(), Some(&4));
    /// assert_eq!(iter.next(), Some(&3));
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn next_back(&mut self) -> Option<Self::Item> {
        let mut current = self.next.as_deref()?;

        if core::ptr::addr_eq(current, self.previous_back) {
            return None;
        }

        while let Some(next) = current.next.as_deref() {
            if core::ptr::addr_eq(next, self.previous_back) {
                break;
            }

            current = next;
        }

        self.previous_back = current;

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
    previous_back: *const Node<T>,
}

impl<'a, T: 'a> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    /// Obtain the next element from the front, if any.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let mut underlying = Singly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut instance = underlying.iter_mut();
    ///
    /// assert_eq!(iter.next(), Some(&mut 1));
    /// assert_eq!(iter.next(), Some(&mut 2));
    /// assert_eq!(iter.next(), Some(&mut 3));
    /// assert_eq!(iter.next(), Some(&mut 4));
    /// assert_eq!(iter.next(), Some(&mut 5));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        self.next.take().and_then(|current| {
            if core::ptr::addr_eq(current, self.previous_back) {
                None
            } else {
                self.next = current.next.as_deref_mut();
                Some(&mut current.element)
            }
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
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let instance = Singly::from_iter([0, 1, 2, 4, 4, 5]).iter();
    ///
    /// assert_eq!(instance.iter_mut().size_hint(), (6, Some(6)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        let mut count: usize = 0;

        let mut next = self.next.as_deref();

        while let Some(current) = next.take() {
            if let Some(incremented) = count.checked_add(1) {
                count = incremented;
            } else {
                unreachable!("more than usize::MAX elements");
            }

            next = current.next.as_deref();
        }

        (count, Some(count))
    }
}

impl<'a, T: 'a> DoubleEndedIterator for IterMut<'a, T> {
    /// Obtain the next element from the back, if any.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let mut underlying = Singly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut instance = underlying.iter_mut();
    ///
    /// assert_eq!(iter.next(), Some(&mut 5));
    /// assert_eq!(iter.next(), Some(&mut 4));
    /// assert_eq!(iter.next(), Some(&mut 3));
    /// assert_eq!(iter.next(), Some(&mut 2));
    /// assert_eq!(iter.next(), Some(&mut 1));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn next_back(&mut self) -> Option<Self::Item> {
        let mut current_ref = self.next.take()?;
        let mut current_ptr = core::ptr::from_mut(current_ref);

        if core::ptr::addr_eq(current_ref, self.previous_back) {
            return None;
        }

        let old_next = current_ptr;

        while let Some(next) = current_ref.next.as_deref_mut() {
            if core::ptr::addr_eq(next, self.previous_back) {
                break;
            }

            current_ptr = next;
            current_ref = next;
        }

        // SAFETY:
        // `self.previous_back` ensures multiple references to the same
        // elements will not be yielded. However, `self.next` has mutable
        // access to all subsequent elements including the last, hence a
        // mutable reference to the next back cannot be returned without
        // invalidating `self.next`. This exists for pointer misdirection
        // where we manually enforce Rust's lifetime rules to create a mutable
        // reference to the next front node after consuming it to derive the
        // mutable reference to the last node and its element.
        self.next = unsafe { old_next.as_mut() };

        self.previous_back = current_ptr;

        Some(&mut current_ref.element)
    }
}

impl<'a, T: 'a> ExactSizeIterator for IterMut<'a, T> {}

impl<'a, T: 'a> core::iter::FusedIterator for IterMut<'a, T> {}

/// By-value iterator over a range of indices.
struct Drain<'a, T> {
    /// The next element from the front to be yielded, if any.
    next: &'a mut Option<Box<Node<T>>>,

    /// The number of elements yet to be yielded.
    remaining: usize,
}

impl<'a, T: 'a> Drop for Drain<'a, T> {
    /// Remove elements yet to be drained and repair the underlying [`Singly`].
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let instance = Singly::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// core::mem::drop(instance.drain(1..=4));
    ///
    /// assert!(instance.iter().eq([0, 5]));
    /// ```
    fn drop(&mut self) {
        self.for_each(drop);
    }
}

impl<'a, T: 'a> Iterator for Drain<'a, T> {
    type Item = T;

    /// Obtain the next element from the front, if any exists.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let underlying = Singly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let instance = underlying.drain(1..=4);
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

            let removed = self.next.take()?;

            *self.next = removed.next;

            Some(removed.element)
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
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let underlying = Singly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let instance = underlying.drain(1..=4);
    ///
    /// assert_eq!(instance.size_hint(), (4, Some(4)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        let mut count: usize = 0;
        let mut remaining = self.remaining;

        let mut next = self.next.as_deref();

        while let Some(current) = next.take() {
            if let Some(decremented) = remaining.checked_sub(1) {
                remaining = decremented;
            } else {
                break;
            }

            if let Some(incremented) = count.checked_add(1) {
                count = incremented;
            } else {
                unreachable!("more than usize::MAX elements");
            }

            next = current.next.as_deref();
        }

        (count, Some(count))
    }
}

impl<'a, T: 'a> DoubleEndedIterator for Drain<'a, T> {
    /// Obtain the next element from the back, if any exists.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::list::Singly;
    ///
    /// let underlying = Singly::from_iter([0, 1, 2, 3, 4, 5]);
    /// let instance = underlying.drain(1..=4);
    ///
    /// assert_eq!(instance.next_back(), Some(4));
    /// assert_eq!(instance.next_back(), Some(3));
    /// assert_eq!(instance.next_back(), Some(2));
    /// assert_eq!(instance.next_back(), Some(1));
    /// assert_eq!(instance.next_back(), None);
    /// ```
    fn next_back(&mut self) -> Option<Self::Item> {
        self.remaining.checked_sub(1).and_then(|decremented| {
            self.remaining = decremented;

            let mut next = self.next.as_deref_mut();

            for _ in 0..self.remaining {
                if let Some(current) = next.take() {
                    if current.next.is_none() {
                        break;
                    }

                    next = current.next.as_deref_mut();
                } else {
                    break;
                }
            }

            next.and_then(|preceding| {
                let mut removed = preceding.next.take()?;
                let succeeding = removed.next.take();
                preceding.next = succeeding;

                Some(removed.element)
            })
        })
    }
}

impl<'a, T: 'a> ExactSizeIterator for Drain<'a, T> {}

impl<'a, T: 'a> core::iter::FusedIterator for Drain<'a, T> {}

// TODO: examples for withdraw
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

        #[test]
        fn empty() {
            let instance = Singly::<usize>::default();

            drop(instance);
        }

        #[test]
        fn zero_size_type() {
            let instance: Singly<_> = [(), (), (), (), (), ()].into_iter().collect();

            drop(instance);
        }

        #[test]
        fn deallocates_nodes() {
            let instance: Singly<_> = [0, 1, 2, 3, 4, 5].into_iter().collect();

            drop(instance);
        }
    }

    mod default {
        use super::*;

        #[test]
        fn has_no_elements() {
            let instance = Singly::<()>::default();

            assert!(instance.elements.is_none());
        }
    }

    mod clone {
        use super::*;

        #[test]
        fn has_elements() {
            let expected = Singly::from_iter([0, 1, 2, 3, 4, 5]);

            let actual = expected.clone();

            assert_eq!(actual.len(), expected.len());
        }

        #[test]
        fn is_equivalent() {
            let expected = Singly::from_iter([0, 1, 2, 3, 4, 5]);

            let actual = expected.clone();

            assert_eq!(actual, expected);
        }

        #[test]
        #[allow(clippy::shadow_unrelated)]
        fn owns_elements() {
            let original = Singly::from_iter([0, 1, 2, 3, 4, 5]);

            let clone = original.clone();

            for (clone, original) in clone.iter().zip(original.iter()) {
                assert!(!core::ptr::addr_eq(clone, original));
            }
        }
    }

    mod equality {
        use super::*;

        #[test]
        fn eq_when_same_elements() {
            let elements = [0, 1, 2, 3, 4, 5];

            let first: Singly<_> = elements.iter().copied().collect();
            let second: Singly<_> = elements.iter().copied().collect();

            assert_eq!(first, second);
        }

        #[test]
        fn ne_when_different_elements() {
            let first: Singly<_> = [0].into_iter().collect();
            let second: Singly<_> = [1].into_iter().collect();

            assert_ne!(first, second);
        }

        #[test]
        fn is_symmetric() {
            let elements = [0, 1, 2, 3, 4, 5];

            let first: Singly<_> = elements.iter().copied().collect();
            let second: Singly<_> = elements.iter().copied().collect();

            // `first == second` <=> `second == first`
            assert_eq!(first, second);
            assert_eq!(second, first);
        }

        #[test]
        fn is_transitive() {
            let elements = [0, 1, 2, 3, 4, 5];

            let first: Singly<_> = elements.iter().copied().collect();
            let second: Singly<_> = elements.iter().copied().collect();
            let third: Singly<_> = elements.iter().copied().collect();

            // `first == second && second == third` => `first == third`
            assert_eq!(first, second);
            assert_eq!(second, third);
            assert_eq!(third, first);
        }

        #[test]
        fn is_reflexive() {
            let actual = Singly::<()>::default();

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

                let actual: Singly<_> = expected.iter().copied().collect();

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
            let actual = Singly::from_iter(expected);

            for (index, value) in expected.iter().enumerate() {
                assert_eq!(actual.index(index), value);
            }
        }

        #[test]
        #[should_panic = "index out of bounds"]
        fn panics_when_out_of_bounds() {
            let instance = Singly::<()>::default();

            let _: &() = instance.index(0);
        }
    }

    mod index_mut {
        use super::*;
        use core::ops::IndexMut;

        #[test]
        fn correct_element() {
            let expected = [0, 1, 2, 3, 4, 5];
            let mut actual = Singly::from_iter(expected);

            for (index, value) in expected.iter().enumerate() {
                assert_eq!(actual.index_mut(index), value);
            }
        }

        #[test]
        #[should_panic = "index out of bounds"]
        fn panics_when_out_of_bounds() {
            let mut instance = Singly::<()>::default();

            let _: &() = instance.index_mut(0);
        }

        #[test]
        fn is_mutable() {
            let mut instance: Singly<_> = [0, 1, 2, 3, 4, 5].into_iter().collect();

            for index in 0..instance.len() {
                *(instance.index_mut(index)) = 0;
            }

            for element in instance {
                assert_eq!(element, 0);
            }
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
                (isize::MAX as usize, Some(isize::MAX as usize))
            }
        }

        mod into {
            use super::*;

            #[test]
            fn element_count() {
                let expected = [0, 1, 2, 3, 4, 5];

                let actual: Singly<_> = expected.iter().copied().collect();

                assert_eq!(actual.into_iter().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let expected = [0, 1, 2, 3, 4, 5];

                let actual: Singly<_> = expected.iter().copied().collect();

                assert!(actual.into_iter().eq(expected));
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Singly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.into_iter().rev().len(), expected.len());
                }

                #[test]
                fn in_order() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Singly<_> = expected.iter().copied().collect();

                    assert!(actual.into_iter().rev().eq(expected.into_iter().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Singly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.size_hint(), (expected.len(), Some(expected.len())));
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Singly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.size_hint(), (expected.len(), Some(expected.len())));
                }

                #[test]
                fn updates() {
                    let mut actual = Singly::from_iter([0, 1, 2, 3, 4, 5]).into_iter();

                    drop(actual.next());
                    assert_eq!(actual.len(), 5);

                    drop(actual.next());
                    assert_eq!(actual.len(), 4);

                    drop(actual.next());
                    assert_eq!(actual.len(), 3);

                    drop(actual.next());
                    assert_eq!(actual.len(), 2);

                    drop(actual.next());
                    assert_eq!(actual.len(), 1);

                    drop(actual.next());
                    assert_eq!(actual.len(), 0);
                }
            }

            mod fused {
                use super::*;

                #[test]
                fn empty() {
                    let mut actual = Singly::<()>::default().into_iter();

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }

                #[test]
                fn exhausted() {
                    let mut actual = Singly::from_iter([()]).into_iter();

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
                let actual: Singly<()> = core::iter::empty().collect();

                assert!(actual.elements.is_none())
            }

            #[test]
            fn has_elements() {
                let expected = [0, 1, 2, 3, 4, 5];

                let actual: Singly<_> = expected.iter().copied().collect();

                assert_eq!(actual.len(), expected.len());
            }

            #[test]
            fn initializes_elements() {
                let expected = [0, 1, 2, 3, 4, 5];

                let actual: Singly<_> = expected.iter().copied().collect();

                assert!(actual.eq(expected));
            }
        }

        mod extend {
            use super::*;

            #[test]
            fn when_empty() {
                let mut actual = Singly::<usize>::default();

                let expected = [0, 1, 2, 3, 4, 5];

                actual.extend(expected.iter().copied());

                assert!(actual.eq(expected));
            }

            #[test]
            fn has_elements() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual = Singly::<usize>::default();

                actual.extend(expected);

                assert_eq!(actual.len(), expected.len());
            }

            #[test]
            fn initializes_elements() {
                let mut actual: Singly<_> = [0, 1, 2].into_iter().collect();

                actual.extend([3, 4, 5]);

                assert!(actual.eq([0, 1, 2, 3, 4, 5]));
            }

            #[test]
            fn does_not_modify_initialized_elements() {
                let expected = [0, 1, 2];

                let mut actual: Singly<_> = expected.into_iter().collect();

                actual.extend([3, 4, 5]);

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn appends_after_initialized_elements() {
                let initialized = [0, 1, 2, 3, 4, 5];
                let mut actual: Singly<_> = initialized.iter().copied().collect();

                let expected = [6, 7, 8, 9, 10];
                actual.extend(expected.iter().copied());

                for index in initialized.len()..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn empty() {
                let mut actual = Singly::<()>::default();

                actual.extend(core::iter::empty());

                assert!(actual.elements.is_none());
            }

            #[test]
            fn does_not_trust_size_hint() {
                let mut actual = Singly::<usize>::default();

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
                let actual: Singly<_> = [0, 1, 2, 3, 4, 5].into_iter().collect();

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

                let actual: Singly<_> = expected.iter().copied().collect();

                assert_eq!(actual.iter().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let expected = [0, 1, 2, 3, 4, 5];

                let actual: Singly<_> = expected.iter().copied().collect();

                assert!(actual.iter().eq(expected.iter()));
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Singly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.iter().rev().count(), expected.len());
                }

                #[test]
                fn in_order() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Singly<_> = expected.iter().copied().collect();

                    assert!(actual.iter().rev().eq(expected.iter().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Singly<_> = expected.iter().copied().collect();

                    assert_eq!(
                        actual.iter().size_hint(),
                        (expected.len(), Some(expected.len()))
                    );
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Singly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.iter().len(), expected.len());
                }

                #[test]
                fn updates() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual: Singly<_> = expected.iter().copied().collect();

                    let mut actual = actual.iter();

                    drop(actual.next());
                    assert_eq!(actual.len(), 5);

                    drop(actual.next());
                    assert_eq!(actual.len(), 4);

                    drop(actual.next());
                    assert_eq!(actual.len(), 3);

                    drop(actual.next());
                    assert_eq!(actual.len(), 2);

                    drop(actual.next());
                    assert_eq!(actual.len(), 1);

                    drop(actual.next());
                    assert_eq!(actual.len(), 0);
                }
            }

            mod fused {
                use super::*;

                #[test]
                fn empty() {
                    let actual = Singly::<()>::default();

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
                    let actual: Singly<_> = [()].into_iter().collect();

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

                let mut actual: Singly<_> = expected.iter().copied().collect();

                assert_eq!(actual.iter_mut().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual: Singly<_> = expected.iter().copied().collect();

                assert!(actual.iter_mut().eq(expected.iter()));
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let mut actual: Singly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.iter_mut().rev().count(), expected.len());
                }

                #[test]
                fn in_order() {
                    let mut expected = [0, 1, 2, 3, 4, 5];

                    let mut actual: Singly<_> = expected.iter().copied().collect();

                    assert!(actual.iter_mut().rev().eq(expected.iter_mut().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let mut actual: Singly<_> = expected.iter().copied().collect();

                    assert_eq!(
                        actual.iter_mut().size_hint(),
                        (expected.len(), Some(expected.len()))
                    );
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let mut actual: Singly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.iter_mut().len(), expected.len());
                }

                #[test]
                fn updates() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let mut actual: Singly<_> = expected.iter().copied().collect();

                    let mut actual = actual.iter_mut();

                    drop(actual.next());
                    assert_eq!(actual.len(), 5);

                    drop(actual.next());
                    assert_eq!(actual.len(), 4);

                    drop(actual.next());
                    assert_eq!(actual.len(), 3);

                    drop(actual.next());
                    assert_eq!(actual.len(), 2);

                    drop(actual.next());
                    assert_eq!(actual.len(), 1);

                    drop(actual.next());
                    assert_eq!(actual.len(), 0);
                }
            }

            mod fused {
                use super::*;

                #[test]
                fn empty() {
                    let mut actual = Singly::<()>::default();

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
                    let mut actual: Singly<_> = [()].into_iter().collect();

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
    }

    mod list {
        use super::*;

        mod insert {
            use super::*;

            #[test]
            fn adds_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Singly<_> = expected.iter().copied().collect();

                _ = actual.insert(2, 12345).expect("successful allocation");

                assert_eq!(actual.len(), expected.len() + 1);
            }

            #[test]
            fn initializes_element() {
                let mut actual: Singly<_> = [0, 1, 2, 3, 4, 5].into_iter().collect();

                actual.insert(2, 12345);

                assert_eq!(actual[2], 12345);
            }

            #[test]
            fn yields_inserted_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Singly<_> = expected.iter().copied().collect();

                let actual = actual.insert(2, 12345).expect("successful allocation");

                assert_eq!(actual, &mut 12345);
            }

            #[test]
            fn does_not_modify_leading_elements() {
                const INDEX: usize = 2;

                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Singly<_> = expected.iter().copied().collect();

                _ = actual.insert(INDEX, 12345).expect("successful allocation");

                for index in 0..INDEX {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn does_not_modify_trailing_elements() {
                const INDEX: usize = 2;

                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Singly<_> = expected.iter().copied().collect();

                _ = actual.insert(INDEX, 12345).expect("successful allocation");

                for index in INDEX..expected.len() {
                    assert_eq!(actual[index + 1], expected[index]);
                }
            }

            #[test]
            fn when_empty() {
                let mut actual = Singly::<usize>::default();

                assert!(actual.insert(0, 12345).is_ok());
            }

            #[test]
            fn can_prepend() {
                let mut actual: Singly<_> = [0, 1, 2, 3, 4, 5].into_iter().collect();

                assert!(actual.insert(0, 12345).is_ok());

                assert_eq!(actual[0], 12345);
            }

            #[test]
            fn can_append() {
                let mut actual: Singly<_> = [0, 1, 2, 3, 4, 5].into_iter().collect();

                assert!(actual.insert(6, 12345).is_ok());

                assert_eq!(actual[6], 12345);
            }
        }

        mod remove {
            use super::*;

            #[test]
            fn subtracts_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Singly<_> = expected.iter().copied().collect();

                _ = actual.remove(0);

                assert_eq!(actual.len(), expected.len() - 1);
            }

            #[test]
            fn yields_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Singly<_> = expected.iter().copied().collect();

                (0..expected.len()).for_each(|index| {
                    assert_eq!(actual.remove(0).expect("front element"), expected[index]);
                });
            }

            #[test]
            fn does_not_modify_leading_elements() {
                const INDEX: usize = 2;

                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Singly<_> = expected.iter().copied().collect();

                _ = actual.remove(INDEX);

                for index in 0..INDEX {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn does_not_modify_trailing_elements() {
                const INDEX: usize = 2;

                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual: Singly<_> = expected.iter().copied().collect();

                _ = actual.remove(INDEX);

                for index in INDEX..expected.len() - 1 {
                    assert_eq!(actual[index], expected[index + 1]);
                }
            }

            #[test]
            fn none_when_index_out_of_bounds() {
                let mut actual = Singly::<()>::default();

                assert!(actual.remove(0).is_none());
            }
        }

        mod drain {
            use super::*;

            #[test]
            fn none_when_out_of_bounds_range() {
                let mut instance = Singly::from_iter([0, 1, 2, 3, 4, 5]);

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
                    let mut actual: Singly<_> = expected.iter().copied().collect();

                    assert_eq!(actual.drain(1..4).count(), expected.drain(1..4).count());
                }

                #[test]
                fn in_order() {
                    let mut expected = vec![0, 1, 2, 3, 4, 5];
                    let mut actual: Singly<_> = expected.iter().copied().collect();

                    assert!(actual.drain(1..4).eq(expected.drain(1..4)));
                }

                mod double_ended {
                    use super::*;

                    #[test]
                    fn element_count() {
                        let mut expected = vec![0, 1, 2, 3, 4, 5];
                        let mut actual: Singly<_> = expected.iter().copied().collect();

                        assert_eq!(
                            actual.drain(1..4).rev().count(),
                            expected.drain(1..4).rev().count()
                        );
                    }

                    #[test]
                    fn in_order() {
                        let mut expected = vec![0, 1, 2, 3, 4, 5];
                        let mut actual: Singly<_> = expected.iter().copied().collect();

                        assert!(actual.drain(1..4).rev().eq(expected.drain(1..4).rev()));
                    }
                }

                mod exact_size {
                    use super::*;

                    #[test]
                    fn hint() {
                        let mut expected = vec![0, 1, 2, 3, 4, 5];
                        let mut actual: Singly<_> = expected.iter().copied().collect();

                        let expected = expected.drain(1..4);

                        assert_eq!(
                            actual.drain(1..4).size_hint(),
                            (expected.len(), Some(expected.len()))
                        );
                    }

                    #[test]
                    fn len() {
                        let mut expected = vec![0, 1, 2, 3, 4, 5];
                        let mut actual: Singly<_> = expected.iter().copied().collect();

                        assert_eq!(actual.drain(1..4).len(), expected.drain(1..4).len());
                    }
                }

                mod fused {
                    use super::*;

                    #[test]
                    fn empty() {
                        let mut actual = Singly::<()>::default();
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
                        let mut actual: Singly<_> = [()].into_iter().collect();
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
                    let mut actual = Singly::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(..));

                    assert_eq!(actual.len(), 0);
                }

                #[test]
                fn does_not_modify_leading_elements() {
                    let mut actual = Singly::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(3..));

                    assert!(actual.iter().eq([0, 1, 2].iter()));
                }

                #[test]
                fn does_not_modify_trailing_elements() {
                    let mut actual = Singly::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(..3));

                    assert!(actual.iter().eq([3, 4, 5].iter()));
                }

                #[test]
                fn combines_leading_and_trailing_elements() {
                    let mut actual = Singly::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(1..=4));

                    assert!(actual.iter().eq([0, 5].iter()));
                }
            }
        }

        mod withdraw {
            use super::*;

            mod iterator {
                use super::*;

                #[test]
                fn element_count() {
                    let mut underlying = Singly::from_iter([0, 1, 2, 3, 4, 5]);

                    let actual = underlying.withdraw(|element| element % 2 == 0);

                    assert_eq!(actual.count(), 3);
                }

                #[test]
                fn in_order() {
                    let mut underlying = Singly::from_iter([0, 1, 2, 3, 4, 5]);

                    let actual = underlying.withdraw(|element| element % 2 == 0);

                    assert!(actual.eq([0, 2, 4]));
                }

                #[test]
                fn combines_retained_elements() {
                    let mut actual = Singly::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.withdraw(|element| element == &1));

                    assert!(actual.eq([0, 2, 3, 4, 5]));
                }

                #[test]
                fn size_hint() {
                    let mut underlying = Singly::from_iter([0, 1, 2, 3, 4, 5]);

                    let actual = underlying.withdraw(|element| element % 2 == 0);

                    assert_eq!(actual.size_hint(), (0, Some(6)));
                }

                mod double_ended {
                    use super::*;

                    #[test]
                    fn element_count() {
                        let mut underlying = Singly::from_iter([0, 1, 2, 3, 4, 5]);

                        let actual = underlying.withdraw(|element| element % 2 == 0).rev();

                        assert_eq!(actual.count(), 3);
                    }

                    #[test]
                    fn in_order() {
                        let mut underlying = Singly::from_iter([0, 1, 2, 3, 4, 5]);

                        let actual = underlying.withdraw(|element| element % 2 == 0).rev();

                        assert!(actual.eq([4, 2, 0]));
                    }

                    #[test]
                    fn combines_retained_elements() {
                        let mut actual = Singly::from_iter([0, 1, 2, 3, 4, 5]);

                        drop(actual.withdraw(|element| element == &1).rev());

                        assert!(actual.eq([0, 2, 3, 4, 5]));
                    }

                    #[test]
                    fn prevents_elements_from_being_yielded_more_than_once() {
                        let mut underlying = Singly::from_iter([0, 1, 2, 0]);

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
                        let mut underlying = Singly::from_iter([0]);
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
                        let mut underlying = Singly::<usize>::default();
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
                    let mut actual = Singly::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.withdraw(|element| element % 2 == 0));

                    assert!(actual.eq([1, 3, 5]));
                }
            }
        }

        mod clear {
            use super::*;

            #[test]
            fn drop_all_elements() {
                let mut actual = Singly::from_iter([0, 1, 2, 3, 4, 5]);

                actual.clear();

                assert_eq!(actual.len(), 0);
            }

            #[test]
            fn when_already_empty() {
                let mut actual = Singly::<usize>::default();

                // Ideally this will panic or something in case of logic error.
                actual.clear();
            }
        }
    }
}
