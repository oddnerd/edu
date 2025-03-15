//! Implementation of [`Fixed`].

use super::Array;
use super::Collection;
use super::Linear;

/// Fixed size (statically stack allocated) [`Array`].
///
/// [`Fixed`] is equivalent to Rust's primitive array ([`[T; N]`](array)) or
/// C++'s smart array
/// ([`std::array`](https://en.cppreference.com/w/cpp/container/array))
/// which interprets the underlying array as being 'dumb' that eagerly decays
/// to a pointer and wraps it in a object.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Fixed<T, const N: usize> {
    /// Underlying memory buffer.
    data: [T; N],
}

impl<T, const N: usize> From<[T; N]> for Fixed<T, N> {
    /// Construct from an existing [`array`].
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Fixed::from(expected.clone());
    ///
    /// assert!(actual.iter().eq(expected.iter()));
    /// ```
    fn from(array: [T; N]) -> Self {
        Self { data: array }
    }
}

impl<T: Default, const N: usize> Default for Fixed<T, N> {
    /// Construct with default initialized elements.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let actual: Fixed<i32, 256> = Default::default();
    ///
    /// for actual in actual {
    ///     assert_eq!(actual, Default::default());
    /// }
    /// ```
    fn default() -> Self {
        // SAFETY: the [`MaybeUninit<T>`] is initialized even if the `T` isn't.
        let mut uninitialized: [core::mem::MaybeUninit<T>; N] =
            unsafe { core::mem::MaybeUninit::uninit().assume_init() };

        for element in &mut uninitialized {
            _ = element.write(Default::default());
        }

        // SAFETY:
        // * [`MaybeUninit<T>`] has same size as `T` => arrays have same size.
        // * [`MaybeUninit<T>`] has same alignment as `T` => elements aligned.
        let initialized = unsafe { uninitialized.as_mut_ptr().cast::<[T; N]>().read() };

        Self::from(initialized)
    }
}

impl<T, const N: usize> core::ops::Index<usize> for Fixed<T, N> {
    type Output = T;

    /// Query the element `index` positions from the start.
    ///
    /// # Panics
    /// This method has the precondition that the `index` is within bounds.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Fixed::from(expected.clone());
    ///
    /// for index in 0..expected.len() {
    ///     use core::ops::Index;
    ///     assert_eq!(actual.index(index), expected.index(index));
    /// }
    /// ```
    fn index(&self, index: usize) -> &Self::Output {
        debug_assert!(index < N, "index out of bounds");

        let ptr = self.data.as_ptr();

        // SAFETY: index in bounds => aligned within allocated object.
        let ptr = unsafe { ptr.add(index) };

        // SAFETY:
        // * underlying object is initialized => points to initialized `T`.
        // * lifetime bound to input object => valid lifetime to return.
        unsafe { &*ptr }
    }
}

impl<T, const N: usize> core::ops::IndexMut<usize> for Fixed<T, N> {
    /// Obtain a reference to the element `index` positions from the start.
    ///
    /// # Panics
    /// This method has the precondition that the `index` is within bounds.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    /// let mut actual = Fixed::from(expected.clone());
    ///
    /// for index in 0..expected.len() {
    ///     use core::ops::IndexMut;
    ///     assert_eq!(actual.index_mut(index), expected.index_mut(index));
    /// }
    /// ```
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        debug_assert!(index < N, "index out of bounds");

        let ptr = self.data.as_mut_ptr();

        // SAFETY: index in bounds => aligned within allocated object.
        let ptr = unsafe { ptr.add(index) };

        // SAFETY:
        // * underlying object is initialized => points to initialized `T`.
        // * lifetime bound to input object => valid lifetime to return.
        unsafe { &mut *ptr }
    }
}

impl<T, const N: usize> IntoIterator for Fixed<T, N> {
    type Item = T;

    type IntoIter = IntoIter<T, N>;

    /// Obtain an iterator that yields ownership of elements by value.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Fixed::from(expected.clone());
    ///
    /// assert!(actual.into_iter().eq(expected.into_iter()));
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            data: self.data.map(|element| core::mem::ManuallyDrop::new(element)),
            next: 0..N,
        }
    }
}

impl<T: core::fmt::Debug, const N: usize> core::fmt::Debug for Fixed<T, N> {
    /// List the elements referenced to/contained.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Fixed::from(expected.clone());
    ///
    /// assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    /// ```
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T, const N: usize> Collection for Fixed<T, N> {
    type Element = T;

    /// Query how many elements are contained.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::Collection;
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Fixed::from(expected.clone());
    ///
    /// assert_eq!(actual.count(), expected.len());
    /// ```
    fn count(&self) -> usize {
        N
    }
}

impl<T, const N: usize> Linear for Fixed<T, N> {
    /// Immutably iterate the elements in order.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Fixed::from(expected.clone());
    ///
    /// for (actual, expected) in actual.iter().zip(expected.iter()) {
    ///     assert_eq!(actual, expected);
    /// }
    /// ```
    fn iter(
        &self,
    ) -> impl DoubleEndedIterator<Item = &Self::Element> + ExactSizeIterator + core::iter::FusedIterator
    {
        let ptr = {
            // This pointer will _never_ be written to.
            let ptr = self.data.as_ptr().cast_mut();

            // SAFETY: `data` exists => `ptr` is non-null.
            unsafe { core::ptr::NonNull::new_unchecked(ptr) }
        };

        // SAFETY:
        // * Pointer is aligned.
        // * Pointer points to one allocated object.
        // * Points to `N` initialized instance of `T`.
        unsafe { super::Iter::new(ptr, N) }
    }

    /// Mutably iterate the elements in order.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    /// let mut actual = Fixed::from(expected.clone());
    ///
    /// for (actual, expected) in actual.iter_mut().zip(expected.iter_mut()) {
    ///     assert_eq!(actual, expected);
    /// }
    /// ```
    fn iter_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = &mut Self::Element>
           + ExactSizeIterator
           + core::iter::FusedIterator {
        let ptr = {
            // This pointer will _never_ be written to.
            let ptr = self.data.as_ptr().cast_mut();

            // SAFETY: `data` exists => `ptr` is non-null.
            unsafe { core::ptr::NonNull::new_unchecked(ptr) }
        };

        // SAFETY:
        // * Pointer is aligned.
        // * Pointer points to one allocated object.
        // * Points to `N` initialized instance of `T`.
        unsafe { super::IterMut::new(ptr, N) }
    }
}

impl<T, const N: usize> Array for Fixed<T, N> {
    /// Obtain an immutable pointer to the underlying contigious memory buffer.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::Collection;
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::Array;
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let expected = Fixed::from([0, 1, 2, 3, 4, 5]);
    /// let actual = {
    ///     let ptr = expected.as_ptr();
    ///     let len = expected.count();
    ///     unsafe { core::slice::from_raw_parts(ptr, len) }
    /// };
    ///
    /// assert!(actual.iter().eq(expected.iter()));
    /// ```
    fn as_ptr(&self) -> *const Self::Element {
        self.data.as_ptr()
    }

    /// Obtain an mutable pointer to the underlying contigious memory buffer.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::Collection;
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::Array;
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let mut expected = Fixed::from([0, 1, 2, 3, 4, 5]);
    /// let mut actual = {
    ///     let ptr = expected.as_mut_ptr();
    ///     let len = expected.count();
    ///     unsafe { core::slice::from_raw_parts_mut(ptr, len) }
    /// };
    ///
    /// assert!(actual.iter_mut().eq(expected.iter_mut()));
    /// ```
    fn as_mut_ptr(&mut self) -> *mut Self::Element {
        self.data.as_mut_ptr()
    }
}

/// By-value [`Iterator`] over a [`Fixed`].
pub struct IntoIter<T, const N: usize> {
    /// Ownership of the underlying array.
    data: [core::mem::ManuallyDrop<T>; N],

    /// Elements within the range have yet to be yielded.
    next: core::ops::Range<usize>,
}

impl<T: core::fmt::Debug, const N: usize> core::fmt::Debug for IntoIter<T, N> {
    /// Print out the element yet to be yielded.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let mut instance = Fixed::from([0, 1, 2, 3, 4, 5]).into_iter();
    ///
    /// // Remove some elements.
    /// instance.next();
    /// instance.next_back();
    ///
    /// assert_eq!(format!("{instance:?}"), format!("[1, 2, 3, 4]"));
    /// ```
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut list = &mut f.debug_list();

        let ptr = {
            // Will _never_ write to this pointer.
            let ptr = self.data.as_ptr().cast_mut();

            // `ManuallyDrop<T>` has the same memory layout at `T`.
            ptr.cast::<T>()
        };

        for index in self.next.clone() {
            // SAFETY: stays aligned within the allocated object.
            let ptr = unsafe { ptr.add(index) };

            // SAFETY:
            // * Pointer is non-null.
            // * Points to initialized instance of `T`.
            let element = unsafe { &*ptr };

            list = list.entry(element);
        }

        list.finish()
    }
}

impl<T, const N: usize> Drop for IntoIter<T, N> {
    /// Drops the elements that have yet to be yielded.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let mut iter = Fixed::from([0, 1, 2, 3, 4, 5]).into_iter();
    ///
    /// iter.next();      // Consumes the element with value `0`.
    /// iter.next_back(); // Consumes the element with value `5`.
    ///
    /// core::mem::drop(iter); // Drops elements with values `[1, 2, 3, 4]`.
    /// ```
    fn drop(&mut self) {
        for index in self.next.clone() {
            let Some(element) = self.data.get_mut(index) else {
                unreachable!("loop ensures index is within bounds");
            };

            // SAFETY: the element will not be accessed or dropped again.
            unsafe { core::mem::ManuallyDrop::drop(element); }
        }
    }
}

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;

    /// Obtain the next element, if there are any left.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let mut actual = Fixed::from([0, 1, 2, 3, 4, 5]).into_iter();
    ///
    /// assert_eq!(actual.next(), Some(0));
    /// assert_eq!(actual.next(), Some(1));
    /// assert_eq!(actual.next(), Some(2));
    /// assert_eq!(actual.next(), Some(3));
    /// assert_eq!(actual.next(), Some(4));
    /// assert_eq!(actual.next(), Some(5));
    /// assert_eq!(actual.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        self.next.next().map(|index| {
            let Some(element) = self.data.get_mut(index) else {
                unreachable!("`self.next` ensures index is within bounds");
            };

            // SAFETY: the element will never be accessed or dropped again.
            unsafe { core::mem::ManuallyDrop::take(element) }
        })
    }

    /// Query how many elements have yet to be yielded.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Fixed::from(expected).into_iter();
    ///
    /// assert_eq!(actual.size_hint(), expected.into_iter().size_hint());
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.next.size_hint()
    }
}

impl<T, const N: usize> DoubleEndedIterator for IntoIter<T, N> {
    /// Obtain the final element, if there are any left.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let mut actual = Fixed::from([0, 1, 2, 3, 4, 5]).into_iter();
    ///
    /// assert_eq!(actual.next_back(), Some(5));
    /// assert_eq!(actual.next_back(), Some(4));
    /// assert_eq!(actual.next_back(), Some(3));
    /// assert_eq!(actual.next_back(), Some(2));
    /// assert_eq!(actual.next_back(), Some(1));
    /// assert_eq!(actual.next_back(), Some(0));
    /// assert_eq!(actual.next_back(), None);
    /// ```
    fn next_back(&mut self) -> Option<Self::Item> {
        self.next.next_back().map(|index| {
            let array = self.data.as_mut_ptr();

            // SAFETY: stays aligned within the allocated object.
            let element = unsafe { array.add(index) };

            // SAFETY: this takes ownership (move).
            let owned = unsafe { element.read() };

            core::mem::ManuallyDrop::into_inner(owned)
        })
    }
}

impl<T, const N: usize> ExactSizeIterator for IntoIter<T, N> {}

impl<T, const N: usize> core::iter::FusedIterator for IntoIter<T, N> {}

#[cfg(test)]
mod test {
    use super::*;

    mod from {
        use super::*;

        mod primitive_array {
            use super::*;

            #[test]
            fn initializes_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Fixed::from(expected);

                assert_eq!(actual.data, expected);
            }
        }
    }

    mod index {
        use super::*;
        use core::ops::Index as _;

        #[test]
        fn correct_element() {
            let expected = [0, 1, 2, 3, 4, 5];
            let actual = Fixed::from(expected);

            for (index, value) in expected.iter().enumerate() {
                assert_eq!(actual.index(index), value);
            }
        }

        #[test]
        #[should_panic = "index out of bounds"]
        fn panics_when_out_of_bounds() {
            let instance = Fixed::<(), 0>::default();

            let _: &() = instance.index(0);
        }
    }

    mod index_mut {
        use super::*;
        use core::ops::IndexMut as _;

        #[test]
        fn correct_element() {
            let mut expected = [0, 1, 2, 3, 4, 5];
            let mut actual = Fixed::from(expected);

            for (index, value) in expected.iter_mut().enumerate() {
                assert_eq!(actual.index_mut(index), value);
            }
        }

        #[test]
        #[should_panic = "index out of bounds"]
        fn panics_when_out_of_bounds() {
            let mut instance = Fixed::<(), 0>::default();

            let _: &() = instance.index_mut(0);
        }

        #[test]
        fn is_mutable() {
            let mut actual = Fixed::from([0, 1, 2, 3, 4, 5]);

            for index in 0..actual.count() {
                *actual.index_mut(index) = 0;
            }

            for element in actual {
                assert_eq!(element, 0);
            }
        }
    }

    mod iterator {
        use super::*;

        mod into {
            use super::*;

            #[test]
            fn element_count() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Fixed::from(expected);

                assert_eq!(actual.into_iter().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Fixed::from(expected);

                assert!(actual.into_iter().eq(expected.into_iter()));
            }

            #[test]
            fn drops_yet_to_be_yielded_elements() {
                use crate::test::mock::DropCounter;

                const ELEMENTS: usize = 256;

                let dropped = DropCounter::new_counter();

                let actual = Fixed::from(core::array::from_fn::<_, ELEMENTS, _>(|_| DropCounter::new(&dropped)));

                drop(actual.into_iter());

                assert_eq!(dropped.take(), ELEMENTS);
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected);

                    assert_eq!(actual.into_iter().rev().count(), expected.len());
                }

                #[test]
                fn in_order() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected);

                    assert!(actual.into_iter().rev().eq(expected.into_iter().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected);

                    assert_eq!(
                        actual.into_iter().size_hint(),
                        (expected.len(), Some(expected.len()))
                    );
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected);

                    assert_eq!(actual.into_iter().len(), expected.len());
                }

                #[test]
                fn updates() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected);

                    let mut actual = actual.iter();

                    for remaining in (0..expected.len()).rev() {
                        _ = actual.next();

                        assert_eq!(actual.len(), remaining);
                    }
                }
            }

            mod fused {
                use super::*;

                #[test]
                fn empty() {
                    let actual = Fixed::<(), 0>::default();
                    let mut actual = actual.into_iter();

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }

                #[test]
                fn exhausted() {
                    let actual = Fixed::from([()]);
                    let mut actual = actual.into_iter();

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
    }

    mod default {
        use super::*;

        #[derive(Debug, PartialEq, Eq)]
        struct Value {
            underlying: usize,
        }

        impl Default for Value {
            fn default() -> Self {
                Value {
                    underlying: 31_415_926,
                }
            }
        }

        #[test]
        fn initializes_elements() {
            let actual = Fixed::<Value, 256>::default();

            for element in actual {
                assert_eq!(element, Value::default());
            }
        }
    }

    #[allow(clippy::clone_on_copy)]
    mod clone {
        use super::*;

        #[test]
        fn is_equivalent() {
            let expected = Fixed::from([0, 1, 2, 3, 4, 5]);

            let actual = expected.clone();

            assert_eq!(actual, expected);
        }

        #[test]
        fn owns_elements() {
            let expected = Fixed::from([0, 1, 2, 3, 4, 5]);

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
            let expected = [0, 1, 2, 3, 4, 5];

            let first = Fixed::from(expected);
            let second = Fixed::from(expected);

            assert_eq!(first, second);
        }

        #[test]
        fn ne_when_different_elements() {
            let first = Fixed::from([0]);
            let second = Fixed::from([1]);

            assert_ne!(first, second);
        }

        #[test]
        fn is_symmetric() {
            let expected = [0, 1, 2, 3, 4, 5];

            let first = Fixed::from(expected);
            let second = Fixed::from(expected);

            // `first == second` <=> `second == first`
            assert_eq!(first, second);
            assert_eq!(second, first);
        }

        #[test]
        fn is_transitive() {
            let expected = [0, 1, 2, 3, 4, 5];

            let first = Fixed::from(expected);
            let second = Fixed::from(expected);
            let third = Fixed::from(expected);

            // `first == second && second == third` => `first == third`
            assert_eq!(first, second);
            assert_eq!(second, third);
            assert_eq!(third, first);
        }

        #[test]
        fn is_reflexive() {
            let actual = Fixed::<(), 0>::default();

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
                let actual = Fixed::from(expected);

                assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
            }
        }
    }

    mod collection {
        use super::*;

        mod count {
            use super::*;

            #[test]
            fn initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Fixed::from(expected);

                assert_eq!(Collection::count(&actual), expected.len());
            }

            #[test]
            fn zero_when_empty() {
                let actual = Fixed::<(), 0>::default();

                assert_eq!(Collection::count(&actual), 0);
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
                let actual = Fixed::from(expected);

                assert_eq!(actual.iter().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Fixed::from(expected);

                assert!(actual.iter().eq(expected.iter()));
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected);

                    assert_eq!(actual.iter().rev().count(), expected.len());
                }

                #[test]
                fn in_order() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected);

                    assert!(actual.iter().rev().eq(expected.iter().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected);

                    assert_eq!(
                        actual.iter().size_hint(),
                        (expected.len(), Some(expected.len()))
                    );
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected);

                    assert_eq!(actual.iter().len(), expected.len());
                }

                #[test]
                fn updates() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected);

                    let mut actual = actual.iter();

                    for remaining in (0..expected.len()).rev() {
                        _ = actual.next();

                        assert_eq!(actual.len(), remaining);
                    }
                }
            }

            mod fused {
                use super::*;

                #[test]
                fn empty() {
                    let actual = Fixed::<(), 0>::default();
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
                    let actual = Fixed::from([()]);
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
                let mut actual = Fixed::from(expected);

                assert_eq!(actual.iter_mut().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let mut expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Fixed::from(expected);

                assert!(actual.iter_mut().eq(expected.iter_mut()));
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let mut actual = Fixed::from(expected);

                    assert_eq!(actual.iter_mut().rev().count(), expected.len());
                }

                #[test]
                fn in_order() {
                    let mut expected = [0, 1, 2, 3, 4, 5];
                    let mut actual = Fixed::from(expected);

                    assert!(actual.iter_mut().rev().eq(expected.iter_mut().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let mut actual = Fixed::from(expected);

                    assert_eq!(
                        actual.iter_mut().size_hint(),
                        (expected.len(), Some(expected.len()))
                    );
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let mut actual = Fixed::from(expected);

                    assert_eq!(actual.iter_mut().len(), expected.len());
                }

                #[test]
                fn updates() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let mut actual = Fixed::from(expected);

                    let mut actual = actual.iter_mut();

                    for remaining in (0..expected.len()).rev() {
                        _ = actual.next();

                        assert_eq!(actual.len(), remaining);
                    }
                }
            }

            mod fused {
                use super::*;

                #[test]
                fn empty() {
                    let mut actual = Fixed::<(), 0>::default();
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
                    let mut actual = Fixed::from([()]);
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

    mod array {
        use super::*;

        mod as_ptr {
            use super::*;

            #[test]
            fn correct_address() {
                let actual = Fixed::from([0, 1, 2, 3, 4, 5]);

                assert_eq!(actual.as_ptr(), actual.data.as_ptr());
            }
        }

        mod as_mut_ptr {
            use super::*;

            #[test]
            fn correct_address() {
                let mut actual = Fixed::from([0, 1, 2, 3, 4, 5]);

                assert_eq!(actual.as_mut_ptr(), actual.data.as_mut_ptr());
            }
        }
    }
}
