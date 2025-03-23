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
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Fixed<T, const N: usize> {
    /// Underlying memory buffer.
    data: [T; N],
}

impl<T: Default, const N: usize> Default for Fixed<T, N> {
    /// Construct with default initialized elements.
    ///
    /// # Performance
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(N) | 𝛀(N) | 𝚯(N) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(N) | 𝛀(N) | 𝚯(N) |
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
        Self::from(core::array::from_fn::<_, N, _>(|_| T::default()))
    }
}

impl<T, const N: usize> From<[T; N]> for Fixed<T, N> {
    /// Construct from an existing [`array`].
    ///
    /// # Performance
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(N) | 𝛀(N) | 𝚯(N) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(N) | 𝛀(N) | 𝚯(N) |
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

impl<T, const N: usize> core::ops::Index<usize> for Fixed<T, N> {
    type Output = T;

    /// Obtain a reference to the element `index` positions from the start.
    ///
    /// # Panics
    /// If provided `index` is out of bounds.
    ///
    /// # Performance
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
        assert!(index < N, "index out of bounds");

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
    /// If provided `index` is out of bounds.
    ///
    /// # Performance
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
        assert!(index < N, "index out of bounds");

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
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(N) | 𝛀(N) | 𝚯(N) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(N) | 𝛀(N) | 𝚯(N) |
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
            // SAFETY: [`MaybeUninit<T>`] has same memory layout as `T`.
            data: unsafe { core::mem::transmute_copy(&self.data) },
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

impl<T, const N: usize> Iterator for IntoIter<T, N> {
    type Item = T;

    /// Obtain the next element, if there are any left.
    ///
    /// # Performance
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
            let Some(element) = self.data.get_mut(index) else {
                unreachable!("`self.next` ensures index is within bounds");
            };

            // SAFETY: the element will never be accessed or dropped again.
            unsafe { core::mem::ManuallyDrop::take(element) }
        })
    }
}

impl<T, const N: usize> ExactSizeIterator for IntoIter<T, N> {}

impl<T, const N: usize> core::iter::FusedIterator for IntoIter<T, N> {}

impl<T, const N: usize> Drop for IntoIter<T, N> {
    /// Drops the elements that have yet to be yielded.
    ///
    /// # Performance
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(N) | 𝛀(N) | 𝚯(N) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
            unsafe {
                core::mem::ManuallyDrop::drop(element);
            }
        }
    }
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

#[cfg(test)]
mod test {
    use super::*;

    mod default {
        use super::*;

        #[test]
        fn handles_zero_length() {
            use crate::test::mock::DefaultValue;

            // Ideally, this will panic if it misuses the length.
            _ = Fixed::<DefaultValue, 0>::default();
        }

        #[test]
        fn initializes_elements_to_correct_value_when_non_zero_length() {
            use crate::test::mock::DefaultValue;

            let actual = Fixed::<DefaultValue, 256>::default();

            for element in actual {
                assert_eq!(element, DefaultValue::default());
            }
        }
    }

    mod from {
        use super::*;

        mod array {
            use super::*;

            #[test]
            fn handles_when_input_is_empty() {
                let input: [usize; 0] = [];

                let actual = Fixed::from(input);

                assert!(actual.is_empty());
            }

            #[test]
            fn has_same_elements_in_same_order_when_input_is_not_empty() {
                let expected = [0, 1, 2, 3, 4, 5];

                let actual = expected;
                let actual = Fixed::from(actual);

                assert_eq!(actual.data, expected);
            }

            #[test]
            fn moves_elements_into_self() {
                use crate::test::mock::DropCounter;

                const ELEMENTS: usize = 8;

                let dropped = DropCounter::new_counter();

                let input = core::array::from_fn::<_, ELEMENTS, _>(|_| DropCounter::new(&dropped));

                // The purpose of this test is to ensure elements are moved
                // from the input into self. If this constructor erroneously
                // duplicates elements in some way, then this will increment
                // the counter more than one times the number of elements.
                drop(Fixed::from(input));

                assert_eq!(dropped.take(), ELEMENTS);
            }
        }
    }

    mod partial_equality {
        use super::*;

        #[test]
        fn is_symmetric() {
            // a == b <=> b == a

            let elements = [0, 1, 2, 3, 4, 5];

            let a = Fixed::from(elements);
            let b = Fixed::from(elements);

            assert_eq!(a, b);
            assert_eq!(b, a);
        }

        #[test]
        fn is_transitive() {
            // a == b && b == c <=> a == c

            let elements = [0, 1, 2, 3, 4, 5];

            let a = Fixed::from(elements);
            let b = Fixed::from(elements);
            let c = Fixed::from(elements);

            assert_eq!(a, b);
            assert_eq!(b, c);
            assert_eq!(a, c);
        }

        #[test]
        fn is_equal_when_same_elements_in_same_order() {
            let elements = [0, 1, 2, 3, 4, 5];

            let a = Fixed::from(elements);
            let b = Fixed::from(elements);

            assert_eq!(a, b);
        }

        #[test]
        fn is_equal_when_both_underlyings_are_empty() {
            let elements: [usize; 0] = [];
            debug_assert!(elements.is_empty());

            let a = Fixed::from(elements);
            let b = Fixed::from(elements);

            assert_eq!(a, b);
        }

        #[test]
        fn is_not_equal_when_same_elements_in_different_order() {
            const ELEMENTS: usize = 8;

            let elements = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            let a = Fixed::from(elements);

            for offset in 1..ELEMENTS {
                let mut b = elements;
                b.rotate_right(offset);
                let b = Fixed::from(b);

                assert_ne!(a, b);
            }
        }

        #[test]
        fn is_not_equal_when_an_element_has_a_different_value() {
            const ELEMENTS: usize = 8;

            let elements = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            let a = Fixed::from(elements);

            for index in 0..ELEMENTS {
                let mut b = elements;

                b[index] = 12345; // Some arbitrary distinct value.

                let b = Fixed::from(b);

                assert_ne!(a, b);
            }
        }
    }

    mod equality {
        use super::*;

        #[test]
        fn is_reflexive() {
            // a == a

            let a = Fixed::from([0, 1, 2, 3, 4, 5]);

            assert_eq!(a, a);
        }
    }

    mod index {
        use super::*;

        use core::ops::Index as _;

        #[test]
        #[should_panic = "index out of bounds"]
        fn panics_when_indexing_into_empty_underlying() {
            let underlying: [usize; 0] = [];
            debug_assert!(underlying.is_empty());

            let actual = Fixed::from(underlying);

            _ = actual.index(0);
        }

        #[test]
        #[should_panic = "index out of bounds"]
        fn panics_when_index_is_out_of_bounds() {
            let underlying = [0, 1, 2, 3, 4, 5];
            debug_assert!(!underlying.is_empty());

            let actual = Fixed::from(underlying);

            _ = actual.index(6);
        }

        #[test]
        fn yields_correct_element_when_index_is_inside_bounds() {
            const ELEMENTS: usize = 8;

            let underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            let actual = Fixed::from(underlying);

            for index in 0..ELEMENTS {
                assert_eq!(actual.index(index), &index);
            }
        }
    }

    mod index_mut {
        use super::*;

        use core::ops::IndexMut as _;

        #[test]
        #[should_panic = "index out of bounds"]
        fn panics_when_indexing_into_empty_underlying() {
            let underlying: [usize; 0] = [];
            debug_assert!(underlying.is_empty());

            let mut actual = Fixed::from(underlying);

            _ = actual.index_mut(0);
        }

        #[test]
        #[should_panic = "index out of bounds"]
        fn panics_when_index_is_out_of_bounds() {
            let underlying = [0, 1, 2, 3, 4, 5];
            debug_assert!(!underlying.is_empty());

            let mut actual = Fixed::from(underlying);

            _ = actual.index_mut(6);
        }

        #[test]
        fn yields_correct_element_when_index_is_inside_bounds() {
            const ELEMENTS: usize = 8;

            let underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            let mut actual = Fixed::from(underlying);

            for mut index in 0..ELEMENTS {
                assert_eq!(actual.index_mut(index), &mut index);
            }
        }

        #[test]
        fn underlying_element_is_updated_when_yielded_reference_is_mutated() {
            const ELEMENTS: usize = 8;

            let mut expected = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            let mut actual = Fixed::from(expected);

            for (index, value) in (0..ELEMENTS).rev().enumerate() {
                *actual.index_mut(index) = value;
            }

            expected.reverse();

            assert_eq!(actual.data, expected);
        }
    }

    mod into_iterator {
        use super::*;

        mod iterator {
            use super::*;

            mod next {
                use super::*;

                #[test]
                fn yields_none_when_empty() {
                    let elements: [usize; 0] = [];
                    debug_assert!(elements.is_empty());

                    let mut actual = Fixed::from(elements).into_iter();

                    assert_eq!(actual.next(), None);
                }

                #[test]
                fn can_be_advanced_the_number_of_elements_when_not_empty() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    debug_assert!(!expected.is_empty());

                    let actual = Fixed::from(expected).into_iter();

                    assert_eq!(actual.count(), expected.len());
                }

                #[test]
                fn yields_correct_elements_in_correct_order_when_not_empty() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual = Fixed::from(expected).into_iter();

                    assert!(actual.eq(expected));
                }
            }

            mod size_hint {
                use super::*;

                #[test]
                fn lower_bound_is_number_of_elements_when_constructed() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual = Fixed::from(expected).into_iter();

                    let (lower, _upper) = actual.size_hint();

                    assert_eq!(lower, expected.len());
                }

                #[test]
                fn lower_bound_updates_when_advanced() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let mut actual = Fixed::from(expected).into_iter();

                    #[expect(clippy::shadow_unrelated, reason = "derived from length")]
                    for expected in (0..expected.len()).rev() {
                        _ = actual.next().expect("an element");

                        let (lower, _upper) = actual.size_hint();

                        assert_eq!(lower, expected);
                    }
                }

                #[test]
                fn upper_bound_is_number_of_elements_when_constructed() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let actual = Fixed::from(expected).into_iter();

                    let (_lower, upper) = actual.size_hint();

                    assert_eq!(upper, Some(expected.len()));
                }

                #[test]
                fn upper_bound_updates_when_advanced() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let mut actual = Fixed::from(expected).into_iter();

                    #[expect(clippy::shadow_unrelated, reason = "derived from length")]
                    for expected in (0..expected.len()).rev() {
                        _ = actual.next().expect("an element");

                        let (_lower, upper) = actual.size_hint();

                        assert_eq!(upper, Some(expected));
                    }
                }
            }
        }

        mod double_ended_iterator {
            use super::*;

            mod next_back {
                use super::*;

                #[test]
                fn yields_none_when_empty() {
                    let  expected: [usize; 0] = [];
                    debug_assert!(expected.is_empty());

                    let mut actual = Fixed::from(expected).into_iter().rev();

                    assert_eq!(actual.next(), None);
                }

                #[test]
                fn can_be_advanced_the_number_of_elements_when_not_empty() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    debug_assert!(!expected.is_empty());

                    let actual = Fixed::from(expected).into_iter().rev();

                    assert_eq!(actual.count(), expected.len());
                }

                #[test]
                fn yields_correct_elements_in_correct_order_when_not_empty() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    debug_assert!(!expected.is_empty());

                    let actual = Fixed::from(expected).into_iter().rev();

                    assert!(actual.eq(expected.into_iter().rev()));
                }

                #[test]
                fn prevents_elements_from_being_yielded_more_than_once_when_advanced_from_both_ends() {
                    let underlying = [0, 1];
                    debug_assert!(!underlying.is_empty());

                    let mut actual = Fixed::from(underlying).into_iter().rev();

                    _ = actual.next().expect("consumes element with value 0");
                    _ = actual.next_back().expect("consumes element with value 1");

                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }
            }

            mod size_hint {
                use super::*;

                #[test]
                fn lower_bound_updates_when_advanced() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let mut actual = Fixed::from(expected).into_iter().rev();

                    #[expect(clippy::shadow_unrelated, reason = "derived from length")]
                    for expected in (0..expected.len()).rev() {
                        _ = actual.next().expect("an element");

                        let (lower, _upper) = actual.size_hint();

                        assert_eq!(lower, expected);
                    }
                }

                #[test]
                fn upper_bound_updates_when_advanced() {
                    let expected = [0, 1, 2, 3, 4, 5];

                    let mut actual = Fixed::from(expected).into_iter().rev();

                    #[expect(clippy::shadow_unrelated, reason = "derived from length")]
                    for expected in (0..expected.len()).rev() {
                        _ = actual.next().expect("an element");

                        let (_lower, upper) = actual.size_hint();

                        assert_eq!(upper, Some(expected));
                    }
                }
            }
        }

        mod fuzed_iterator {
            use super::*;

            #[test]
            fn continues_to_yield_none_when_empty() {
                let underlying: [usize; 0] = [];
                debug_assert!(underlying.is_empty());

                let mut actual = Fixed::from(underlying).into_iter();

                // Yields `None` at least once.
                assert_eq!(actual.next(), None);
                assert_eq!(actual.next_back(), None);

                // Continues to yield `None`.
                assert_eq!(actual.next(), None);
                assert_eq!(actual.next_back(), None);
            }

            #[test]
            fn continues_to_yield_none_exhausted() {
                let underlying = [0];

                let mut actual = Fixed::from(underlying).into_iter();

                // Exhaust the elements.
                _ = actual.next().expect("the one element");

                // Yields `None` at least once.
                assert_eq!(actual.next(), None);
                assert_eq!(actual.next_back(), None);

                // Continues to yield `None`.
                assert_eq!(actual.next(), None);
                assert_eq!(actual.next_back(), None);
            }
        }

        mod drop {
            use super::*;

            #[test]
            fn drops_unyielded_elements_when_advanced_from_front() {
                use crate::test::mock::DropCounter;

                const ELEMENTS: usize = 8;

                for yielded in 0..ELEMENTS {
                    let dropped = DropCounter::new_counter();

                    let mut actual =
                        Fixed::from(core::array::from_fn::<_, ELEMENTS, _>(|_| {
                            DropCounter::new(&dropped)
                        }))
                        .into_iter();

                    for _ in 0..yielded {
                        // Lifetime is passed to caller.
                        drop(actual.next());
                    }

                    // The above drops in caller scope, not the
                    // destructor being tested, so reset counter.
                    debug_assert_eq!(dropped.replace(0), yielded);

                    // Now we drop the iterator, so we expect all
                    // remaining elements to be dropped.
                    drop(actual);

                    assert_eq!(dropped.take(), ELEMENTS - yielded);
                }
            }

            #[test]
            fn drops_unyielded_elements_when_advanced_from_back() {
                use crate::test::mock::DropCounter;

                const ELEMENTS: usize = 8;

                for yielded in 0..ELEMENTS {
                    let dropped = DropCounter::new_counter();

                    let mut actual =
                        Fixed::from(core::array::from_fn::<_, ELEMENTS, _>(|_| {
                            DropCounter::new(&dropped)
                        }))
                        .into_iter();

                    for _ in 0..yielded {
                        // Lifetime is passed to caller.
                        drop(actual.next_back());
                    }

                    // The above drops in caller scope, not the
                    // destructor being tested, so reset counter.
                    debug_assert_eq!(dropped.replace(0), yielded);

                    // Now we drop the iterator, so we expect all
                    // remaining elements to be dropped.
                    drop(actual);

                    assert_eq!(dropped.take(), ELEMENTS - yielded);
                }
            }

            #[test]
            fn drops_unyielded_elements_when_advanced_from_both_ends() {
                use crate::test::mock::DropCounter;

                const ELEMENTS: usize = 8;

                for front in 0..ELEMENTS {
                    for back in front..ELEMENTS {
                        let dropped = DropCounter::new_counter();

                        let mut actual =
                            Fixed::from(core::array::from_fn::<_, ELEMENTS, _>(|_| {
                                DropCounter::new(&dropped)
                            }))
                            .into_iter();

                        for _ in 0..front {
                            // Lifetime is passed to caller.
                            drop(actual.next());
                        }

                        for _ in front..back {
                            // Lifetime is passed to caller.
                            drop(actual.next_back());
                        }

                        // The above drops in caller scope, not the
                        // destructor being tested, so reset counter.
                        let expected = ELEMENTS - dropped.replace(0);

                        // Now we drop the iterator, so we expect all
                        // remaining elements to be dropped.
                        drop(actual);

                        assert_eq!(dropped.take(), expected);
                    }
                }
            }
        }

        mod debug {
            use super::*;

            #[test]
            fn is_an_empty_list_when_empty() {
                let expected: [usize; 0] = [];
                debug_assert!(expected.is_empty());

                let actual = Fixed::from(expected).into_iter();

                assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
            }

            #[test]
            fn is_a_list_of_the_correct_elements_in_the_correct_order_when_not_empty() {
                let expected = [0, 1, 2, 3, 4, 5];
                debug_assert!(!expected.is_empty());

                let actual = Fixed::from(expected).into_iter();

                assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
            }

            #[test]
            fn does_not_contain_elements_yielded_from_the_front() {
                let expected = [0, 1, 2, 3, 4, 5];
                debug_assert!(!expected.is_empty());

                let mut actual = Fixed::from(expected).into_iter();

                for start in 1..=expected.len() {
                    _ = actual.next().expect("an element");

                    let expected = &expected[start..];

                    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
                }
            }

            #[test]
            fn does_not_contain_elements_yielded_from_the_back() {
                let expected = [0, 1, 2, 3, 4, 5];
                debug_assert!(!expected.is_empty());

                let mut actual = Fixed::from(expected).into_iter();

                for end in (0..expected.len()).rev() {
                    _ = actual.next_back().expect("an element");

                    let expected = &expected[..end];

                    assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
                }
            }
        }
    }

    mod debug {
        use super::*;

        #[test]
        fn is_an_empty_list_when_empty() {
            let expected: [usize; 0] = [];
            debug_assert!(expected.is_empty());

            let actual = Fixed::from(expected);

            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        }

        #[test]
        fn is_a_list_of_the_correct_elements_in_the_correct_order_when_not_empty() {
            let expected = [0, 1, 2, 3, 4, 5];
            debug_assert!(!expected.is_empty());

            let actual = Fixed::from(expected);

            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        }
    }

    mod collection {
        use super::*;

        mod count {
            use super::*;

            #[test]
            fn is_zero_when_underlying_is_empty() {
                let expected: [usize; 0] = [];
                debug_assert!(expected.is_empty());

                let actual = Fixed::from(expected);

                assert_eq!(actual.count(), expected.len());
            }

            #[test]
            fn is_number_of_elements_when_underlying_is_not_empty() {
                const ELEMENTS: usize = 8;

                let expected = core::array::from_fn::<_, ELEMENTS, _>(|index| index);
                debug_assert!(!expected.is_empty());

                let actual = Fixed::from(expected);

                assert_eq!(actual.count(), expected.len());
            }
        }
    }

    mod linear {
        use super::*;

        mod iter {
            use super::*;

            mod iterator {
                use super::*;

                mod next {
                    use super::*;

                    #[test]
                    fn yields_none_when_empty() {
                        let actual = Fixed::<usize, 0>::from([]);
                        debug_assert!(actual.data.is_empty());

                        let mut actual = actual.iter();

                        assert_eq!(actual.next(), None);
                    }

                    #[test]
                    fn can_be_advanced_the_number_of_elements_when_not_empty() {
                        let expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let actual = Fixed::from(expected);
                        let actual = actual.iter();

                        assert_eq!(actual.count(), expected.len());
                    }

                    #[test]
                    fn yields_correct_elements_in_correct_order_when_not_empty() {
                        let expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let actual = Fixed::from(expected);
                        let actual = actual.iter();

                        assert!(actual.eq(expected.iter()));
                    }
                }

                mod size_hint {
                    use super::*;

                    #[test]
                    fn lower_bound_is_number_of_elements_when_constructed() {
                        let expected = [0, 1, 2, 3, 4, 5];

                        let actual = Fixed::from(expected);
                        let actual = actual.iter();

                        let (lower, _upper) = actual.size_hint();

                        assert_eq!(lower, expected.len());
                    }

                    #[test]
                    fn lower_bound_updates_when_advanced() {
                        const ELEMENTS: usize = 8;

                        let actual = Fixed::from(core::array::from_fn::<_, ELEMENTS, _>(|index| index));
                        let mut actual = actual.iter();

                        for expected in (0..ELEMENTS).rev() {
                            _ = actual.next().expect("an element");

                            let (lower, _upper) = actual.size_hint();

                            assert_eq!(lower, expected);
                        }
                    }

                    #[test]
                    fn upper_bound_is_number_of_elements_when_constructed() {
                        let expected = [0, 1, 2, 3, 4, 5];

                        let actual = Fixed::from(expected);
                        let actual = actual.iter();

                        let (_lower, upper) = actual.size_hint();

                        assert_eq!(upper, Some(expected.len()));
                    }

                    #[test]
                    fn upper_bound_updates_when_advanced() {
                        const ELEMENTS: usize = 8;

                        let actual = Fixed::from(core::array::from_fn::<_, ELEMENTS, _>(|index| index));
                        let mut actual = actual.iter();

                        for expected in (0..ELEMENTS).rev() {
                            _ = actual.next().expect("an element");

                            let (_lower, upper) = actual.size_hint();

                            assert_eq!(upper, Some(expected));
                        }
                    }
                }
            }

            mod double_ended_iterator {
                use super::*;

                mod next_back {
                    use super::*;

                    #[test]
                    fn yields_none_when_empty() {
                        let actual = Fixed::<usize, 0>::from([]);
                        debug_assert!(actual.data.is_empty());

                        let mut actual = actual.iter().rev();

                        assert_eq!(actual.next(), None);
                    }

                    #[test]
                    fn can_be_advanced_the_number_of_elements_when_not_empty() {
                        let expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let actual = Fixed::from(expected);
                        let actual = actual.iter().rev();

                        assert_eq!(actual.count(), expected.len());
                    }

                    #[test]
                    fn yields_correct_elements_in_correct_order_when_not_empty() {
                        let expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let actual = Fixed::from(expected);
                        let actual = actual.iter().rev();

                        assert!(actual.eq(expected.iter().rev()));
                    }

                    #[test]
                    fn prevents_elements_from_being_yielded_more_than_once_when_advanced_from_both_ends() {
                        let actual = Fixed::from([0, 1]);
                        let mut actual = actual.iter();

                        _ = actual.next().expect("consumes element with value 0");
                        _ = actual.next_back().expect("consumes element with value 1");

                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }
                }

                mod size_hint {
                    use super::*;

                    #[test]
                    fn lower_bound_updates_when_advanced() {
                        const ELEMENTS: usize = 8;

                        let actual = Fixed::from(core::array::from_fn::<_, ELEMENTS, _>(|index| index));
                        let mut actual = actual.iter().rev();

                        for expected in (0..ELEMENTS).rev() {
                            _ = actual.next().expect("an element");

                            let (lower, _upper) = actual.size_hint();

                            assert_eq!(lower, expected);
                        }
                    }

                    #[test]
                    fn upper_bound_updates_when_advanced() {
                        const ELEMENTS: usize = 8;

                        let actual = Fixed::from(core::array::from_fn::<_, ELEMENTS, _>(|index| index));
                        let mut actual = actual.iter().rev();

                        for expected in (0..ELEMENTS).rev() {
                            _ = actual.next().expect("an element");

                            let (_lower, upper) = actual.size_hint();

                            assert_eq!(upper, Some(expected));
                        }
                    }
                }
            }

            mod fused_iterator {
                use super::*;

                #[test]
                fn continues_to_yield_none_when_empty() {
                    let actual = Fixed::<usize, 0>::from([]);
                    debug_assert!(actual.data.is_empty());

                    let mut actual = actual.iter();

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }

                #[test]
                fn continues_to_yield_none_when_exhausted() {
                    let actual = Fixed::from([0]);
                    let mut actual = actual.iter();

                    // Exhaust the elements.
                    _ = actual.next().expect("the one element");

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

            mod iterator {
                use super::*;

                mod next {
                    use super::*;

                    #[test]
                    fn yields_none_when_empty() {
                        let mut actual = Fixed::<usize, 0>::from([]);
                        debug_assert!(actual.data.is_empty());

                        let mut actual = actual.iter_mut();

                        assert_eq!(actual.next(), None);
                    }

                    #[test]
                    fn can_be_advanced_the_number_of_elements_when_not_empty() {
                        let expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let mut actual = Fixed::from(expected);
                        let actual = actual.iter_mut();

                        assert_eq!(actual.count(), expected.len());
                    }

                    #[test]
                    fn yields_correct_elements_in_correct_order_when_not_empty() {
                        let mut expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let mut actual = Fixed::from(expected);
                        let actual = actual.iter_mut();

                        assert!(actual.eq(expected.iter_mut()));
                    }

                    #[test]
                    fn underlying_element_is_updated_when_yielded_reference_is_mutated() {
                        const ELEMENTS: usize = 8;

                        let mut expected = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                        let mut actual = Fixed::from(expected);
                        let mut iter = actual.iter_mut();

                        for value in (0..ELEMENTS).rev() {
                            let element = iter.next().expect("an element");

                            *element = value;
                        }

                        drop(iter);

                        expected.reverse();

                        assert_eq!(actual.data, expected);
                    }
                }

                mod size_hint {
                    use super::*;

                    #[test]
                    fn lower_bound_is_number_of_elements_when_constructed() {
                        let expected = [0, 1, 2, 3, 4, 5];

                        let mut actual = Fixed::from(expected);
                        let actual = actual.iter_mut();

                        let (lower, _upper) = actual.size_hint();

                        assert_eq!(lower, expected.len());
                    }

                    #[test]
                    fn lower_bound_updates_when_advanced() {
                        const ELEMENTS: usize = 8;

                        let mut actual = Fixed::from(core::array::from_fn::<_, ELEMENTS, _>(|index| index));
                        let mut actual = actual.iter_mut();

                        for expected in (0..ELEMENTS).rev() {
                            _ = actual.next().expect("an element");

                            let (lower, _upper) = actual.size_hint();

                            assert_eq!(lower, expected);
                        }
                    }

                    #[test]
                    fn upper_bound_is_number_of_elements_when_constructed() {
                        let expected = [0, 1, 2, 3, 4, 5];

                        let mut actual = Fixed::from(expected);
                        let actual = actual.iter_mut();

                        let (_lower, upper) = actual.size_hint();

                        assert_eq!(upper, Some(expected.len()));
                    }

                    #[test]
                    fn upper_bound_updates_when_advanced() {
                        const ELEMENTS: usize = 8;

                        let mut actual = Fixed::from(core::array::from_fn::<_, ELEMENTS, _>(|index| index));
                        let mut actual = actual.iter_mut();

                        for expected in (0..ELEMENTS).rev() {
                            _ = actual.next().expect("an element");

                            let (_lower, upper) = actual.size_hint();

                            assert_eq!(upper, Some(expected));
                        }
                    }
                }
            }

            mod double_ended_iterator {
                use super::*;

                mod next_back {
                    use super::*;

                    #[test]
                    fn yields_none_when_empty() {
                        let mut actual = Fixed::<usize, 0>::from([]);
                        debug_assert!(actual.data.is_empty());

                        let mut actual = actual.iter_mut().rev();

                        assert_eq!(actual.next(), None);
                    }

                    #[test]
                    fn can_be_advanced_the_number_of_elements_when_not_empty() {
                        let expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let mut actual = Fixed::from(expected);
                        let actual = actual.iter_mut().rev();

                        assert_eq!(actual.count(), expected.len());
                    }

                    #[test]
                    fn yields_correct_elements_in_correct_order_when_not_empty() {
                        let expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let mut actual = Fixed::from(expected);
                        let actual = actual.iter_mut().rev();

                        assert!(actual.eq(expected.iter().rev()));
                    }

                    #[test]
                    fn prevents_elements_from_being_yielded_more_than_once_when_advanced_from_both_ends() {
                        let mut actual = Fixed::from([0, 1]);
                        let mut actual = actual.iter_mut();

                        _ = actual.next().expect("consumes element with value 0");
                        _ = actual.next_back().expect("consumes element with value 1");

                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }

                    #[test]
                    fn underlying_element_is_updated_when_yielded_reference_is_mutated() {
                        const ELEMENTS: usize = 8;

                        let mut expected = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                        let mut actual = Fixed::from(expected);
                        let mut iter = actual.iter_mut().rev();

                        for value in 0..ELEMENTS {
                            let element = iter.next().expect("an element");

                            *element = value;
                        }

                        drop(iter);

                        expected.reverse();

                        assert_eq!(actual.data, expected);
                    }
                }

                mod size_hint {
                    use super::*;

                    #[test]
                    fn lower_bound_updates_when_advanced() {
                        const ELEMENTS: usize = 8;

                        let mut actual = Fixed::from(core::array::from_fn::<_, ELEMENTS, _>(|index| index));
                        let mut actual = actual.iter_mut().rev();

                        for expected in (0..ELEMENTS).rev() {
                            _ = actual.next().expect("an element");

                            let (lower, _upper) = actual.size_hint();

                            assert_eq!(lower, expected);
                        }
                    }

                    #[test]
                    fn upper_bound_updates_when_advanced() {
                        const ELEMENTS: usize = 8;

                        let mut actual = Fixed::from(core::array::from_fn::<_, ELEMENTS, _>(|index| index));
                        let mut actual = actual.iter_mut().rev();

                        for expected in (0..ELEMENTS).rev() {
                            _ = actual.next().expect("an element");

                            let (_lower, upper) = actual.size_hint();

                            assert_eq!(upper, Some(expected));
                        }
                    }
                }
            }

            mod fused_iterator {
                use super::*;

                #[test]
                fn continues_to_yield_none_when_is_empty() {
                    let mut actual = Fixed::<usize, 0>::from([]);
                    debug_assert!(actual.data.is_empty());

                    let mut actual = actual.iter_mut();

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }

                #[test]
                fn continues_to_yield_none_when_exhausted() {
                    let mut actual = Fixed::from([0]);
                    let mut actual = actual.iter_mut();

                    // Exhaust the elements.
                    _ = actual.next().expect("the one element");

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
            fn is_correct_address_when_empty() {
                let actual = Fixed::<usize, 0>::from([]);
                debug_assert!(actual.data.is_empty());

                assert_eq!(actual.as_ptr(), actual.data.as_ptr());
            }

            #[test]
            fn is_correct_address_when_not_empty() {
                let actual = Fixed::from([0, 1, 2, 3, 4, 5]);
                debug_assert!(!actual.data.is_empty());

                assert_eq!(actual.as_ptr(), actual.data.as_ptr());
            }
        }

        mod as_mut_ptr {
            use super::*;

            #[test]
            fn is_correct_address_when_empty() {
                let mut actual = Fixed::<usize, 0>::from([]);
                debug_assert!(actual.data.is_empty());

                assert_eq!(actual.as_mut_ptr(), actual.data.as_mut_ptr());
            }

            #[test]
            fn is_correct_address_when_not_empty() {
                let mut actual = Fixed::from([0, 1, 2, 3, 4, 5]);
                debug_assert!(!actual.data.is_empty());

                assert_eq!(actual.as_mut_ptr(), actual.data.as_mut_ptr());
            }

            #[test]
            fn underlying_element_is_updated_when_yielded_pointer_is_mutated() {
                const ELEMENTS: usize = 8;

                let mut expected = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                let mut actual = Fixed::from(expected);

                for (index, value) in (0..ELEMENTS).rev().enumerate() {
                    let ptr = actual.as_mut_ptr();

                    // We are testing that this is safe.
                    let element = unsafe { ptr.add(index) };

                    // Ideally, this will panic if unowned memory.
                    unsafe { element.write(value); }
                }

                expected.reverse();

                assert_eq!(actual.data, expected);
            }
        }
    }
}
