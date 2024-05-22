//! Implementation of [`Doubly`].

extern crate alloc;

use core::ptr::NonNull;

use super::Collection;
use super::Linear;
use super::List;

/// Independently allocated elements connected via two links.
///
/// Each element exists within separate allocated object, referred to as a
/// node. Each node contains a pointer to the previous node alongside a pointer
/// to the subsequent node whereas [`Self`] maintains a pointer to the first
/// _and_ last node as visualized below:
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
    /// let instance = Singly::from_iter([0, 1, 2, 3, 4, 5]);
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
    /// todo!("assert element count is zero")
    /// ```
    fn default() -> Self {
        Doubly {
            head: None,
            tail: None,
        }
    }
}

impl<T: Clone> Clone for Doubly<T> {
    fn clone(&self) -> Self {
        todo!()
    }
}

impl<T: PartialEq> PartialEq for Doubly<T> {
    fn eq(&self, other: &Self) -> bool {
        todo!()
    }
}

impl<T: Eq> Eq for Doubly<T> {}

impl<T: core::fmt::Debug> core::fmt::Debug for Doubly<T> {
    fn fmt(&self, output: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        todo!()
    }
}

impl<T> core::ops::Index<usize> for Doubly<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        todo!()
    }
}

impl<T> core::ops::IndexMut<usize> for Doubly<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        todo!()
    }
}

impl<T> Iterator for Doubly<T> {
    type Item = T;

    /// Obtain the first element by value via moving it out of [`Self`].
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
        self.head.map(|removed| {
            // SAFETY: the node was allocated via `Box`.
            let removed = unsafe { Box::from_raw(removed.as_ptr()) };

            self.head = removed.successor;

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
    /// Obtain the last element by value via moving it out of [`Self`].
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
        self.tail.map(|removed| {
            // SAFETY: the node was allocated via `Box`.
            let removed = unsafe { Box::from_raw(removed.as_ptr()) };

            self.tail = removed.predecessor;

            removed.element
        })
    }
}

impl<T> ExactSizeIterator for Doubly<T> {}

impl<T> core::iter::FusedIterator for Doubly<T> {}

impl<T> Extend<T> for Doubly<T> {
    /// Append the `elements` at the end, maintaining order.
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
        let mut previous = self.tail;

        let mut next = if let Some(mut tail) = self.tail {
            // SAFETY: aligned to an initialized node that we own.
            let tail = unsafe { tail.as_mut() };

            &mut tail.successor
        } else {
            &mut self.tail
        };

        for element in elements {
            let mut node = {
                let node = Box::new(Node {
                    element,
                    predecessor: previous,
                    successor: None,
                });

                // SAFETY: since allocation has not failed, this cannot be null.
                unsafe { NonNull::new_unchecked(Box::into_raw(node)) }
            };

            _ = next.insert(node);

            previous = Some(node);

            next = {
                // SAFETY: aligned to an initialized node that we own.
                let node = unsafe { node.as_mut() };

                &mut node.successor
            };
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
    /// let actual = Singly::from_iter(expected.iter().copied());
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

            // SAFETY: aligned to an initialized element that we own.
            let current = unsafe { current.as_ref() };

            next = current.successor;
        }

        count
    }
}

impl<T> Linear for Doubly<T> {
    fn iter(
        &self,
    ) -> impl DoubleEndedIterator<Item = &Self::Element> + ExactSizeIterator + core::iter::FusedIterator
    {
        Iter {
            lifetime: core::marker::PhantomData,
        }
    }

    fn iter_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = &mut Self::Element>
           + ExactSizeIterator
           + core::iter::FusedIterator {
        IterMut {
            lifetime: core::marker::PhantomData,
        }
    }
}

impl<T> List for Doubly<T> {
    fn insert(
        &mut self,
        index: usize,
        element: Self::Element,
    ) -> Result<&mut Self::Element, Self::Element> {
        todo!()
    }

    fn remove(&mut self, index: usize) -> Option<Self::Element> {
        todo!()
    }

    fn drain(
        &mut self,
        range: impl core::ops::RangeBounds<usize>,
    ) -> impl DoubleEndedIterator<Item = Self::Element> + ExactSizeIterator {
        Drain {
            lifetime: core::marker::PhantomData,
        }
    }

    fn withdraw(
        &mut self,
        predicate: impl FnMut(&Self::Element) -> bool,
    ) -> impl DoubleEndedIterator<Item = Self::Element> {
        Withdraw {
            lifetime: core::marker::PhantomData,
        }
    }
}

struct Iter<'a, T> {
    lifetime: core::marker::PhantomData<&'a T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        todo!()
    }
}

impl<T> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {}

impl<T> core::iter::FusedIterator for Iter<'_, T> {}

struct IterMut<'a, T> {
    lifetime: core::marker::PhantomData<&'a mut T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        todo!()
    }
}

impl<T> DoubleEndedIterator for IterMut<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<T> ExactSizeIterator for IterMut<'_, T> {}

impl<T> core::iter::FusedIterator for IterMut<'_, T> {}

struct Drain<'a, T> {
    lifetime: core::marker::PhantomData<&'a mut T>,
}

impl<T> Drop for Drain<'_, T> {
    fn drop(&mut self) {
        todo!()
    }
}

impl<T> Iterator for Drain<'_, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        todo!()
    }
}

impl<T> DoubleEndedIterator for Drain<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<T> ExactSizeIterator for Drain<'_, T> {}

impl<T> core::iter::FusedIterator for Drain<'_, T> {}

struct Withdraw<'a, T> {
    lifetime: core::marker::PhantomData<&'a mut T>,
}

impl<T> Drop for Withdraw<'_, T> {
    fn drop(&mut self) {
        todo!()
    }
}

impl<T> Iterator for Withdraw<'_, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        todo!()
    }
}

impl<T> DoubleEndedIterator for Withdraw<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<T> ExactSizeIterator for Withdraw<'_, T> {}

impl<T> core::iter::FusedIterator for Withdraw<'_, T> {}

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
        fn deallocates_nodes() {
            const ELEMENTS: usize = 256;

            let dropped = alloc::rc::Rc::new(core::cell::RefCell::new(usize::default()));

            let mut actual = Doubly::<Droppable>::default();

            for _ in 0..ELEMENTS {
                _ = actual
                    .prepend(Droppable {
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
}
