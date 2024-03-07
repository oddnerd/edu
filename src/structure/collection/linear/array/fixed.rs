//! Implementation of [`Fixed`].

use super::Array;
use super::Collection;
use super::Linear;

/// Fixed size (statically stack allocated) [`Array`].
///
/// [`Fixed`] is equivalent to Rust's primitive array (`[T; N]`) or C++'s
/// smart array (`std::array`) which interprets the underlying array as being
/// 'dumb' that eagerly decays to a pointer and wraps it in a object.
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

impl<'a, T: 'a, const N: usize> Linear<'a> for Fixed<T, N> {
    fn iter(&self) -> impl std::iter::Iterator<Item = &'a Self::Element> {
        unsafe {
            // SAFETY: will be consumed by immutable iterator despite cast.
            let ptr = self.data.as_ptr().cast_mut();

            // SAFETY: `data` exists => pointer will be non-null.
            let ptr = std::ptr::NonNull::new_unchecked(ptr);

            // SAFETY: requirements enforced by underlying array.
            super::iter::Iter::new(ptr, N)
        }
    }

    fn iter_mut(&mut self) -> impl std::iter::Iterator<Item = &'a mut Self::Element> {
        unsafe {
            let ptr = self.data.as_mut_ptr();

            // SAFETY: `data` exists => pointer will be non-null.
            let ptr = std::ptr::NonNull::new_unchecked(ptr);

            // SAFETY: requirements enforced by underlying array.
            super::iter::IterMut::new(ptr, N)
        }
    }

    fn first(&self) -> Option<&Self::Element> {
        if N > 0 {
            Some(&self[0])
        } else {
            None
        }
    }

    fn last(&self) -> Option<&Self::Element> {
        if N > 0 {
            Some(&self[N - 1])
        } else {
            None
        }
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

impl<T, const N: usize> std::ops::Deref for Fixed<T, N> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // SAFETY:
        // * `data` is initialized => every element is initialized.
        // * `data` is one object => slice is over one allocated object.
        unsafe { std::slice::from_raw_parts(self.data.as_ptr(), N) }
    }
}

impl<T, const N: usize> std::ops::DerefMut for Fixed<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY:
        // * `data` is initialized => every element is initialized.
        // * `data` is one object => slice is over one allocated object.
        unsafe { std::slice::from_raw_parts_mut(self.data.as_mut_ptr(), N) }
    }
}

impl<'a, T: 'a, const N: usize> Array<'a> for Fixed<T, N> {}

impl<T: PartialEq, const N: usize> PartialEq for Fixed<T, N> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T: Eq, const N: usize> std::cmp::Eq for Fixed<T, N> {}

impl<T: std::fmt::Debug, const N: usize> std::fmt::Debug for Fixed<T, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
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

impl<T: Clone, const N: usize> Clone for Fixed<T, N> {
    fn clone(&self) -> Self {
        // SAFETY: the [`MaybeUninit`] is initialized even if the `T` isn't.
        let mut uninitialized: [std::mem::MaybeUninit<T>; N] =
            unsafe { std::mem::MaybeUninit::uninit().assume_init() };

        for (from, to) in self.iter().zip(uninitialized.iter_mut()) {
            to.write(from.clone());
        }

        // SAFETY:
        // * [`MaybeUninit<T>`] has same size as `T` => arrays have same size.
        // * [`MaybeUninit<T>`] has same alignment as `T` => elements aligned.
        let initialized = unsafe { uninitialized.as_mut_ptr().cast::<[T; N]>().read() };

        Self::from(initialized)
    }
}

impl<T: Copy, const N: usize> Copy for Fixed<T, N> {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new() {
        let array = [0, 1, 2, 3];
        let instance = Fixed::from(array);

        assert_eq!(instance.data, array);
    }

    #[test]
    fn count() {
        let array = [0, 1, 2, 3];
        let instance = Fixed::from(array);

        assert_eq!(instance.count(), array.len());
    }

    #[test]
    fn into_iter() {
        let array = [0, 1, 2, 3];
        let instance = Fixed::from(array);

        assert!(instance.into_iter().eq(array.into_iter()));
    }

    #[test]
    fn iter() {
        let array = [0, 1, 2, 3];
        let instance = Fixed::from(array);

        assert!(instance.iter().eq(array.iter()));
    }

    #[test]
    fn iter_mut() {
        let mut array = [0, 1, 2, 3];
        let mut instance = Fixed::from(array);

        assert!(instance.iter_mut().eq(array.iter_mut()));
    }

    #[test]
    fn first() {
        let array = [0, 1, 2, 3];
        let instance = Fixed::from(array);

        assert_eq!(*instance.first().unwrap(), instance[0]);
    }

    #[test]
    fn last() {
        let array = [0, 1, 2, 3];
        let instance = Fixed::from(array);

        assert_eq!(*instance.last().unwrap(), instance[3]);
    }

    #[test]
    fn index() {
        let array = [0, 1, 2, 3];
        let instance = Fixed::from(array);

        assert_eq!(instance[0], 0);
        assert_eq!(instance[1], 1);
        assert_eq!(instance[2], 2);
        assert_eq!(instance[3], 3);
    }

    #[test]
    fn index_mut() {
        let array = [0, 1, 2, 3];
        let mut instance = Fixed::from(array);

        instance[0] = 4;
        instance[1] = 5;
        instance[2] = 6;
        instance[3] = 7;

        assert_eq!(instance[0], 4);
        assert_eq!(instance[1], 5);
        assert_eq!(instance[2], 6);
        assert_eq!(instance[3], 7);
    }

    #[test]
    fn deref() {
        let array = [0, 1, 2, 3];
        let instance = Fixed::from(array);

        use std::ops::Deref;
        assert_eq!(*instance.deref(), *array.as_slice());
    }

    #[test]
    fn deref_mut() {
        let array = [0, 1, 2, 3];
        let mut instance = Fixed::from(array);

        use std::ops::DerefMut;
        assert_eq!(*instance.deref_mut(), *array.as_slice());
    }

    #[test]
    fn eq() {
        let array = [0, 1, 2, 3];
        let instance = Fixed::from(array);
        let other = Fixed::from(array);

        assert_eq!(instance, other);
    }

    #[test]
    fn ne() {
        let array = [0, 1, 2, 3];
        let instance = Fixed::from(array);

        let other_array = [4, 5, 6, 7];
        let other = Fixed::from(other_array);

        assert_ne!(instance, other);
    }

    #[test]
    fn default() {
        let array: Fixed<i32, 0> = Default::default();
        assert_eq!(array.count(), 0);

        let array: Fixed<i32, 1> = Default::default();
        assert_eq!(array.count(), 1);
        assert_eq!(array[0], Default::default());

        let array: Fixed<i32, 256> = Default::default();
        assert_eq!(array.count(), 256);
        for element in array {
            assert_eq!(element, Default::default());
        }
    }

    #[test]
    fn clone() {
        let old = Fixed::from([0, 1, 2, 3]);
        let from = old.clone();
        assert_eq!(old, from);
    }
}
