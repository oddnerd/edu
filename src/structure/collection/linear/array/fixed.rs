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
    fn from(array: [T; N]) -> Self {
        Self { data: array }
    }
}

impl<'a, T: 'a, const N: usize> Collection<'a> for Fixed<T, N> {
    type Element = T;

    fn count(&self) -> usize {
        N
    }
}

impl<T, const N: usize> std::ops::Index<usize> for Fixed<T, N> {
    type Output = T;

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
    fn iter(&self) -> impl std::iter::Iterator<Item = &'a Self::Element> {
        unsafe {
            // SAFETY: will never be written to.
            let ptr = self.data.as_ptr().cast_mut();

            // SAFETY: `data` exists => `ptr` is non-null.
            let ptr = std::ptr::NonNull::new_unchecked(ptr);

            super::Iter::new(ptr, N)
        }
    }

    fn iter_mut(&mut self) -> impl std::iter::Iterator<Item = &'a mut Self::Element> {
        unsafe {
            let ptr = self.data.as_mut_ptr();

            // SAFETY: `data` exists => `ptr` is non-null.
            let ptr = std::ptr::NonNull::new_unchecked(ptr);

            super::IterMut::new(ptr, N)
        }
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

impl<'a, T: 'a, const N: usize> std::iter::IntoIterator for Fixed<T, N> {
    type Item = T;

    type IntoIter = IntoIter<T, N>;

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

impl<'a, T: 'a, const N: usize> Array<'a> for Fixed<T, N> {
    unsafe fn as_ptr(&self) -> *const Self::Element {
        self.data.as_ptr()
    }

    unsafe fn as_mut_ptr(&mut self) -> *mut Self::Element {
        self.data.as_mut_ptr()
    }
}

impl<T: Default, const N: usize> std::default::Default for Fixed<T, N> {
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
    fn iter_yields_element_count() {
        let primitive = [0, 1, 2, 3, 4, 5];
        let instance = Fixed::from(primitive);

        assert_eq!(instance.iter().count(), primitive.len());
    }

    #[test]
    fn iter_yields_elements() {
        let primitive = [0, 1, 2, 3, 4, 5];
        let instance = Fixed::from(primitive);

        assert!(instance.iter().eq(primitive.iter()));
    }

    #[test]
    fn iter_mut_yields_element_count() {
        let primitive = [0, 1, 2, 3, 4, 5];
        let mut instance = Fixed::from(primitive);

        assert_eq!(instance.iter_mut().count(), primitive.len());
    }

    #[test]
    fn iter_mut_yields_elements() {
        let mut primitive = [0, 1, 2, 3, 4, 5];
        let mut instance = Fixed::from(primitive);

        assert!(instance.iter_mut().eq(primitive.iter_mut()));
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
