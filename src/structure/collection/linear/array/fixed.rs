//! Implementation of [`Fixed`].

use super::Array;
use super::Collection;
use super::Linear;

/// Fixed size (statically stack allocated) [`Array`].
///
/// [`Fixed`] is equivalent to Rust's primitive array (`[T; N]`) or C++'s
/// smart array (`std::array`) which interprets the underlying array as being
/// 'dumb' that eagerly decays to a pointer and wraps it in a object.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Fixed<T, const N: usize> {
    /// Underlying memory buffer.
    data: [T; N],
}

impl<T, const N: usize> std::convert::From<[T; N]> for Fixed<T, N> {
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
    fn iter(&self) -> impl std::iter::DoubleEndedIterator<Item = &'a Self::Element> + std::iter::ExactSizeIterator + std::iter::FusedIterator {
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
    fn iter_mut(&mut self) -> impl std::iter::DoubleEndedIterator<Item = &'a mut Self::Element> + std::iter::ExactSizeIterator + std::iter::FusedIterator {
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
    unsafe fn as_ptr(&self) -> *const Self::Element {
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
    unsafe fn as_mut_ptr(&mut self) -> *mut Self::Element {
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

impl<T, const N: usize> std::ops::Drop for IntoIter<T, N> {
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

impl<T, const N: usize> std::iter::Iterator for IntoIter<T, N> {
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
}

impl<'a, T: 'a, const N: usize> std::iter::DoubleEndedIterator for IntoIter<T, N> {
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
                Some(std::mem::ManuallyDrop::into_inner(unsafe { element.read() }))
            }
            None => None,
        }
    }
}

impl<'a, T: 'a, const N: usize> std::iter::ExactSizeIterator for IntoIter<T, N> {}

impl<'a, T: 'a, const N: usize> std::iter::FusedIterator for IntoIter<T, N> {}

impl<'a, T: 'a, const N: usize> std::iter::IntoIterator for Fixed<T, N> {
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

impl<T: Default, const N: usize> std::default::Default for Fixed<T, N> {
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
            element.write(Default::default());
        }

        // SAFETY:
        // * [`MaybeUninit<T>`] has same size as `T` => arrays have same size.
        // * [`MaybeUninit<T>`] has same alignment as `T` => elements aligned.
        let initialized = unsafe { uninitialized.as_mut_ptr().cast::<[T; N]>().read() };

        Self::from(initialized)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn from_array_initializes_elements() {
        let primitive = [0, 1, 2, 3, 4, 5];
        let instance = Fixed::from(primitive);

        assert_eq!(instance.data, primitive);
    }

    #[test]
    fn count_is_element_count() {
        let instance = Fixed::from([(), (), (), (), (), ()]);

        assert_eq!(instance.count(), instance.data.len());
    }

    #[test]
    fn index_yields_correct_element() {
        let primitive = [0, 1, 2, 3, 4, 5];
        let instance = Fixed::from(primitive);

        for (index, value) in primitive.iter().enumerate() {
            use std::ops::Index;
            assert_eq!(instance.index(index), value);
        }
    }

    #[test]
    #[should_panic]
    fn index_panics_when_out_of_bounds() {
        let instance = Fixed::<(), 0>::default();

        use std::ops::Index;
        instance.index(0);
    }

    #[test]
    fn index_mut_yields_correct_element() {
        let mut primitive = [0, 1, 2, 3, 4, 5];
        let mut instance = Fixed::from(primitive);

        for (index, value) in primitive.iter_mut().enumerate() {
            use std::ops::IndexMut;
            assert_eq!(instance.index_mut(index), value);
        }
    }

    #[test]
    #[should_panic]
    fn index_mut_panics_when_out_of_bounds() {
        let mut instance = Fixed::<(), 0>::default();

        use std::ops::IndexMut;
        instance.index_mut(0);
    }

    #[test]
    fn as_ptr_is_valid_to_read_all_elements() {
        let primitive = [0, 1, 2, 3, 4, 5];
        let instance = Fixed::from(primitive.clone());

        let slice = unsafe { std::slice::from_raw_parts(instance.as_ptr(), instance.count()) };

        assert_eq!(slice, primitive.as_slice());
    }

    #[test]
    fn as_mut_ptr_is_valid_to_write_all_elements() {
        let primitive = [0, 1, 2, 3, 4, 5];
        let mut instance = Fixed::from(primitive.clone());

        let slice =
            unsafe { std::slice::from_raw_parts_mut(instance.as_mut_ptr(), instance.count()) };

        for (expected, actual) in slice.iter_mut().zip(primitive) {
            assert_eq!(*expected, actual);

            *expected = 0;
        }
    }

    #[test]
    fn eq_for_same_elements() {
        let primitive = [0, 1, 2, 3, 4, 5];
        let instance = Fixed::from(primitive);
        let other = Fixed::from(primitive);

        assert_eq!(instance, other);
    }

    #[test]
    fn ne_for_different_elements() {
        let instance = Fixed::from([0]);
        let other = Fixed::from([1]);

        assert_ne!(instance, other);
    }

    #[test]
    fn into_iter_yields_element_count() {
        let primitive = [0, 1, 2, 3, 4, 5];
        let instance = Fixed::from(primitive);

        assert_eq!(instance.into_iter().count(), primitive.len());
    }

    #[test]
    fn into_iter_yields_elements() {
        let primitive = [0, 1, 2, 3, 4, 5];
        let instance = Fixed::from(primitive);

        assert!(instance.into_iter().eq(primitive.into_iter()));
    }

    #[test]
    fn default_makes_all_elements_default() {
        struct Value(i32);

        impl std::default::Default for Value {
            fn default() -> Self {
                Value(12345)
            }
        }

        let instance: Fixed<Value, 256> = Default::default();

        for value in instance {
            assert_eq!(value.0, Value::default().0);
        }
    }

    #[test]
    fn clone_is_eq() {
        let original = Fixed::from([0, 1, 2, 3, 4, 5]);
        let clone = original.clone();

        assert_eq!(clone, original);
    }
}
