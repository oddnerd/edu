//! Implementation of [`Fixed`].

use super::Array;
use super::Collection;
use super::Linear;

/// Fixed size (statically stack allocated) [`Array`].
///
/// [`Fixed`] is equivalent to Rust's primitive array (`[T; N]`) or C++'s
/// smart array (`std::array`) which interprets the underlying array as being
/// 'dumb' that eagerly decays to a pointer and wraps it in a object.
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
    /// use rust::structure::collection::linear::Linear;
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
        let mut uninitialized: [std::mem::MaybeUninit<T>; N] =
            unsafe { std::mem::MaybeUninit::uninit().assume_init() };

        for element in uninitialized.iter_mut() {
            let _ = element.write(Default::default());
        }

        // SAFETY:
        // * [`MaybeUninit<T>`] has same size as `T` => arrays have same size.
        // * [`MaybeUninit<T>`] has same alignment as `T` => elements aligned.
        let initialized = unsafe { uninitialized.as_mut_ptr().cast::<[T; N]>().read() };

        Self::from(initialized)
    }
}

impl<T, const N: usize> std::ops::Index<usize> for Fixed<T, N> {
    type Output = T;

    /// Query the element `index` positions from the start.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Fixed::from(expected.clone());
    ///
    /// for index in 0..expected.len() {
    /// use std::ops::Index;
    ///     assert_eq!(actual.index(index), expected.index(index));
    /// }
    /// ```
    fn index(&self, index: usize) -> &Self::Output {
        debug_assert!(index < N);
        // SAFETY:
        // * `index` index bounds => pointer is aligned within allocated object.
        // * underlying object is initialized => points to initialized `T`.
        // * lifetime bound to input object => valid lifetime to return.
        unsafe { &*self.data.as_ptr().add(index) }
    }
}

impl<T, const N: usize> std::ops::IndexMut<usize> for Fixed<T, N> {
    /// Obtain a reference to the element `index` positions from the start.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    /// let mut actual = Fixed::from(expected.clone());
    ///
    /// for index in 0..expected.len() {
    ///     use std::ops::IndexMut;
    ///     assert_eq!(actual.index_mut(index), expected.index_mut(index));
    /// }
    /// ```
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        debug_assert!(index < N);
        // SAFETY:
        // * `index` index bounds => pointer is aligned within allocated object.
        // * underlying object is initialized => points to initialized `T`.
        // * lifetime bound to input object => valid lifetime to return.
        unsafe { &mut *self.data.as_mut_ptr().add(index) }
    }
}

impl<'a, T: 'a, const N: usize> IntoIterator for Fixed<T, N> {
    type Item = T;

    type IntoIter = IntoIter<T, N>;

    /// Obtain an iterator that yields ownership of elements by value.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Fixed::from(expected.clone());
    ///
    /// assert!(actual.into_iter().eq(expected.into_iter()));
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            // SAFETY: [`ManuallyDrop<T>`] has same memory layout as `T`.
            data: unsafe {
                self.data
                    .as_ptr()
                    .cast::<[std::mem::ManuallyDrop<T>; N]>()
                    .read()
            },

            next: 0..N,
        }
    }
}

impl<T: std::fmt::Debug, const N: usize> std::fmt::Debug for Fixed<T, N> {
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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<'a, T: 'a, const N: usize> Collection<'a> for Fixed<T, N> {
    type Element = T;

    /// Query how many elements are contained.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Collection;
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

impl<'a, T: 'a, const N: usize> Linear<'a> for Fixed<T, N> {
    /// Immutably iterate the elements in order.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
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
    ) -> impl DoubleEndedIterator<Item = &'a Self::Element> + ExactSizeIterator + std::iter::FusedIterator
    {
        unsafe {
            // SAFETY: will never be written to.
            let ptr = self.data.as_ptr().cast_mut();

            // SAFETY: `data` exists => `ptr` is non-null.
            let ptr = std::ptr::NonNull::new_unchecked(ptr);

            super::Iter::new(ptr, N)
        }
    }

    /// Mutably iterate the elements in order.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
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
    ) -> impl DoubleEndedIterator<Item = &'a mut Self::Element>
           + ExactSizeIterator
           + std::iter::FusedIterator {
        unsafe {
            let ptr = self.data.as_mut_ptr();

            // SAFETY: `data` exists => `ptr` is non-null.
            let ptr = std::ptr::NonNull::new_unchecked(ptr);

            super::IterMut::new(ptr, N)
        }
    }
}

impl<'a, T: 'a, const N: usize> Array<'a> for Fixed<T, N> {
    /// Obtain an immutable pointer to the underlying contigious memory buffer.
    ///
    /// # Safety
    /// * `self` must outlive the resultant pointer.
    /// * Cannot write to resultant pointer or any pointer derived from it.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Collection;
    /// use rust::structure::collection::linear::Linear;
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let expected = Fixed::from([0, 1, 2, 3, 4, 5]);
    /// let actual = unsafe { std::slice::from_raw_parts(expected.as_ptr(), expected.count()) };
    ///
    /// assert!(actual.iter().eq(expected.iter()));
    /// ```
    fn as_ptr(&self) -> *const Self::Element {
        self.data.as_ptr()
    }

    /// Obtain an immutable pointer to the underlying contigious memory buffer.
    ///
    /// # Safety
    /// * `self` must outlive the resultant pointer.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Collection;
    /// use rust::structure::collection::linear::Linear;
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let mut expected = Fixed::from([0, 1, 2, 3, 4, 5]);
    /// let mut actual = unsafe { std::slice::from_raw_parts_mut(expected.as_mut_ptr(), expected.count()) };
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
    data: [std::mem::ManuallyDrop<T>; N],

    /// Elements within the range have yet to be yielded.
    next: std::ops::Range<usize>,
}

impl<T, const N: usize> Drop for IntoIter<T, N> {
    /// Drops the elements that have yet to be yielded.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
    /// use rust::structure::collection::linear::array::Fixed;
    ///
    /// let mut iter = Fixed::from([0, 1, 2, 3, 4, 5]).into_iter();
    ///
    /// iter.next();      // Consumes the element with value `0`.
    /// iter.next_back(); // Consumes the element with value `5`.
    ///
    /// std::mem::drop(iter); // Drops the elements with values `[1, 2, 3, 4]`.
    /// ```
    fn drop(&mut self) {
        for offset in self.next.clone() {
            let ptr = self.data.as_mut_ptr();

            // SAFETY: `T` has the same memory layout as [`ManuallyDrop<T>`].
            let ptr = ptr.cast::<T>();

            // SAFETY: stays aligned within the allocated object.
            let ptr = unsafe { ptr.add(offset) };

            // SAFETY:
            // * owns underlying array => valid for reads and writes.
            // * within `self.next` => pointing to initialized value.
            unsafe { ptr.drop_in_place() };
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
    /// use rust::structure::collection::linear::Linear;
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
        match self.next.next() {
            Some(index) => {
                let array = self.data.as_mut_ptr();

                // SAFETY: stays aligned within the allocated object.
                let element = unsafe { array.add(index) };

                // SAFETY: within bounds => pointing to initialized value.
                let owned = unsafe { element.read() };

                Some(std::mem::ManuallyDrop::into_inner(owned))
            }
            None => None,
        }
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

impl<'a, T: 'a, const N: usize> DoubleEndedIterator for IntoIter<T, N> {
    /// Obtain the final element, if there are any left.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
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
        match self.next.next_back() {
            Some(index) => {
                let array = self.data.as_mut_ptr();

                // SAFETY: stays aligned within the allocated object.
                let element = unsafe { array.add(index) };

                // SAFETY: within bounds => pointing to initialized value.
                Some(std::mem::ManuallyDrop::into_inner(unsafe {
                    element.read()
                }))
            }
            None => None,
        }
    }
}

impl<'a, T: 'a, const N: usize> ExactSizeIterator for IntoIter<T, N> {}

impl<'a, T: 'a, const N: usize> std::iter::FusedIterator for IntoIter<T, N> {}

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
                let actual = Fixed::from(expected.clone());

                assert_eq!(actual.data, expected);
            }
        }
    }

    mod index {
        use super::*;
        use std::ops::Index;

        #[test]
        fn correct_element() {
            let expected = [0, 1, 2, 3, 4, 5];
            let actual = Fixed::from(expected.clone());

            for (index, expected) in expected.iter().enumerate() {
                assert_eq!(actual.index(index), expected);
            }
        }

        #[test]
        #[should_panic]
        fn panics_when_out_of_bounds() {
            let instance = Fixed::<(), 0>::default();

            instance.index(0);
        }
    }

    mod index_mut {
        use super::*;
        use std::ops::IndexMut;

        #[test]
        fn correct_element() {
            let mut expected = [0, 1, 2, 3, 4, 5];
            let mut actual = Fixed::from(expected.clone());

            for (index, expected) in expected.iter_mut().enumerate() {
                assert_eq!(actual.index_mut(index), expected);
            }
        }

        #[test]
        #[should_panic]
        fn panics_when_out_of_bounds() {
            let mut instance = Fixed::<(), 0>::default();

            instance.index_mut(0);
        }
    }

    mod iterator {
        use super::*;

        mod into {
            use super::*;

            #[test]
            fn element_count() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Fixed::from(expected.clone());

                assert_eq!(actual.into_iter().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Fixed::from(expected.clone());

                assert!(actual.into_iter().eq(expected.into_iter()));
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected.clone());

                    assert_eq!(actual.into_iter().rev().count(), expected.len());
                }

                #[test]
                fn in_order() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected.clone());

                    assert!(actual.into_iter().rev().eq(expected.into_iter().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected.clone());

                    assert_eq!(
                        actual.into_iter().size_hint(),
                        (expected.len(), Some(expected.len()))
                    );
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected.clone());

                    assert_eq!(actual.into_iter().len(), expected.len());
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
                    actual.next();

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
                    underlying: 31415926,
                }
            }
        }

        #[test]
        fn initializes_elements() {
            let actual = Fixed::<usize, 256>::default();

            for element in actual {
                assert_eq!(element, Default::default());
            }
        }
    }

    mod clone {
        use super::*;

        #[test]
        fn is_equivalent() {
            let expected = Fixed::from([0, 1, 2, 3, 4, 5]);

            let actual = expected.clone();

            assert_eq!(actual, expected);
        }
    }

    mod equality {
        use super::*;

        #[test]
        fn eq_when_same_elements() {
            let expected = [0, 1, 2, 3, 4, 5];

            let first = Fixed::from(expected.clone());
            let second = Fixed::from(expected.clone());

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

            let first = Fixed::from(expected.clone());
            let second = Fixed::from(expected.clone());

            // `first == second` <=> `second == first`
            assert_eq!(first, second);
            assert_eq!(second, first);
        }

        #[test]
        fn is_transitive() {
            let expected = [0, 1, 2, 3, 4, 5];

            let first = Fixed::from(expected.clone());
            let second = Fixed::from(expected.clone());
            let third = Fixed::from(expected.clone());

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
                let actual = Fixed::from(expected.clone());

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
                let actual = Fixed::from(expected.clone());

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
                let actual = Fixed::from(expected.clone());

                assert_eq!(actual.iter().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Fixed::from(expected.clone());

                assert!(actual.iter().eq(expected.iter()));
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected.clone());

                    assert_eq!(actual.iter().rev().count(), expected.len());
                }

                #[test]
                fn in_order() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected.clone());

                    assert!(actual.iter().rev().eq(expected.iter().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected.clone());

                    assert_eq!(
                        actual.iter().size_hint(),
                        (expected.len(), Some(expected.len()))
                    );
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Fixed::from(expected.clone());

                    assert_eq!(actual.iter().len(), expected.len());
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
                    actual.next();

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
                let mut actual = Fixed::from(expected.clone());

                assert_eq!(actual.iter_mut().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let mut expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Fixed::from(expected.clone());

                assert!(actual.iter_mut().eq(expected.iter_mut()));
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let mut actual = Fixed::from(expected.clone());

                    assert_eq!(actual.iter_mut().rev().count(), expected.len());
                }

                #[test]
                fn in_order() {
                    let mut expected = [0, 1, 2, 3, 4, 5];
                    let mut actual = Fixed::from(expected.clone());

                    assert!(actual.iter_mut().rev().eq(expected.iter_mut().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let mut actual = Fixed::from(expected.clone());

                    assert_eq!(
                        actual.iter_mut().size_hint(),
                        (expected.len(), Some(expected.len()))
                    );
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let mut actual = Fixed::from(expected.clone());

                    assert_eq!(actual.iter_mut().len(), expected.len());
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
                    actual.next();

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
