//! Implementation of [`Dope`].

use super::Array;
use super::Collection;
use super::Linear;

/// Lightweight access to a contagious buffer of memory.
///
/// A [Dope Vector](https://en.wikipedia.org/wiki/Dope_vector) comprises of a
/// pointer and length pair leveraging compile-time type information alongside
/// pointer arithmetic to distinguish between individual elements.
///
/// [`Dope`] is equivalent to Rust's slice (`[T]`) or C++'s span (`std::span`)
/// and views (`std::string_view`).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Dope<'a, T: 'a> {
    /// Pointer to the start of the array.
    ptr: std::ptr::NonNull<T>,

    /// Number of elements within the array.
    count: usize,

    /// Bind lifetime to underlying memory buffer.
    lifetime: std::marker::PhantomData<&'a mut T>,
}

impl<'a, T: 'a> Dope<'a, T> {
    /// Construct from a pointer to an array and the number of elements.
    ///
    /// # Safety
    /// * `ptr` must have an address aligned for access to `T`.
    /// * `ptr` must point to one contigious allocated object.
    /// * `ptr` must point to `len` consecutive initialized instances of `T`.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut underlying = [0, 1, 2, 3, 4, 5];
    /// let ptr = std::ptr::NonNull::new(underlying.as_mut_ptr()).unwrap();
    /// let dope = unsafe { Dope::new(ptr, underlying.len()) };
    ///
    /// assert!(underlying.iter().eq(dope.iter()));
    /// ```
    pub unsafe fn new(ptr: std::ptr::NonNull<T>, count: usize) -> Self {
        Self {
            ptr,
            count,
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> std::convert::From<&'a [T]> for Dope<'a, T> {
    fn from(slice: &'a [T]) -> Self {
        Self {
            ptr: {
                let ptr = slice.as_ptr().cast_mut();

                // SAFETY: `slice` exists => pointer is non-null.
                unsafe { std::ptr::NonNull::new_unchecked(ptr) }
            },
            count: slice.len(),
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> Collection<'a> for Dope<'a, T> {
    type Element = T;

    fn count(&self) -> usize {
        self.count
    }
}

impl<'a, T> std::iter::IntoIterator for Dope<'a, T> {
    type Item = &'a T;

    type IntoIter = super::iter::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        // SAFETY: points to `count` initialized instances of `T`.
        unsafe { super::iter::Iter::new(self.ptr, self.count) }
    }
}

impl<'a, T: 'a> Linear<'a> for Dope<'a, T> {
    fn iter(&self) -> impl std::iter::Iterator<Item = &'a Self::Element> {
        // SAFETY:
        // * `self.data` points to one contigious allocated object.
        // * `self.len` consecutive initialized and aligned instances.
        unsafe { super::iter::Iter::new(self.ptr, self.count) }
    }

    fn iter_mut(&mut self) -> impl std::iter::Iterator<Item = &'a mut Self::Element> {
        // SAFETY:
        // * `self.data` points to one contigious allocated object.
        // * `self.len` consecutive initialized and aligned instances.
        unsafe { super::iter::IterMut::new(self.ptr, self.count) }
    }

    fn first(&self) -> Option<&Self::Element> {
        if !self.is_empty() {
            // SAFETY:
            // * constructor contract => pointed to `T` is initialized.
            // * constructor contract => valid lifetime to return.
            unsafe { Some(self.ptr.as_ref()) }
        } else {
            None
        }
    }

    fn last(&self) -> Option<&Self::Element> {
        if !self.is_empty() {
            let ptr = self.ptr.as_ptr();

            // SAFETY: points to the final element within the allocated object.
            let ptr = unsafe { ptr.add(self.count - 1) };

            // SAFETY:
            // * constructor contract => pointed to `T` is initialized.
            // * constructor contract => valid lifetime to return.
            unsafe { Some(&*ptr) }
        } else {
            None
        }
    }
}

impl<'a, T: 'a> std::ops::Index<usize> for Dope<'a, T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        // SAFETY: stays aligned within the allocated object.
        let ptr = unsafe {
            assert!(index < self.count);
            self.ptr.as_ptr().add(index)
        };

        // SAFETY:
        // * constructor contract => pointed to `T` is initialized.
        // * lifetime bound to input object => valid lifetime to return.
        unsafe { &*ptr }
    }
}

impl<'a, T: 'a> std::ops::IndexMut<usize> for Dope<'a, T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        // SAFETY: stays aligned within the allocated object.
        let ptr = unsafe {
            assert!(index < self.count);
            self.ptr.as_ptr().add(index)
        };

        // SAFETY:
        // * constructor contract => pointed to `T` is initialized.
        // * lifetime bound to input object => valid lifetime to return.
        unsafe { &mut *ptr }
    }
}

impl<'a, T: 'a> std::ops::Deref for Dope<'a, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // SAFETY:
        // * constructor contract => `self.data` is aligned.
        // * constructor contract => every element is initialized.
        // * constructor contract => slice is over one allocated object.
        unsafe { std::slice::from_raw_parts(self.ptr.as_ptr(), self.count) }
    }
}

impl<'a, T: 'a> std::ops::DerefMut for Dope<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY:
        // * constructor contract => `self.data` is aligned.
        // * constructor contract => every element is initialized.
        // * constructor contract => slice is over one allocated object.
        unsafe { std::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.count) }
    }
}

impl<'a, T: 'a> Array<'a> for Dope<'a, T> {}

impl<'a, T: 'a + std::fmt::Debug> std::fmt::Debug for Dope<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new_normal_type() {
        let array = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert_eq!(instance.ptr.as_ptr(), array.as_ptr().cast_mut());
        assert_eq!(instance.count, array.len());
    }

    #[test]
    fn new_zero_size_type() {
        let array = [(), (), (), (), (), ()];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert_eq!(instance.ptr.as_ptr(), array.as_ptr().cast_mut());
        assert_eq!(instance.count, array.len());
    }

    #[test]
    fn from_slice_of_normal_type() {
        let array = [0, 1, 2, 3, 4, 5];
        let instance = Dope::from(array.as_slice());

        assert_eq!(instance.ptr.as_ptr(), array.as_slice().as_ptr().cast_mut());
        assert_eq!(instance.count, array.as_slice().len());
    }

    #[test]
    fn from_slice_of_zero_size_type() {
        let array = [(), (), (), (), (), ()];
        let instance = Dope::from(array.as_slice());

        assert_eq!(instance.ptr.as_ptr(), array.as_slice().as_ptr().cast_mut());
        assert_eq!(instance.count, array.as_slice().len());
    }

    #[test]
    fn count_normal_type() {
        let array = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert_eq!(instance.count(), array.len());
    }

    #[test]
    fn count_zero_size_type() {
        let array = [(), (), (), (), (), ()];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert_eq!(instance.count(), array.len());
    }

    #[test]
    fn into_iter_of_normal_type() {
        let mut array = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert!(instance.into_iter().copied().eq(array.into_iter()));
    }

    #[test]
    fn into_iter_of_zero_size_type() {
        let mut array = [(), (), (), (), (), ()];
        let instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert!(instance.into_iter().copied().eq(array.into_iter()));
    }

    #[test]
    fn iter_normal_type() {
        let array = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert!(instance.iter().eq(array.iter()));
    }

    #[test]
    fn iter_zero_size_type() {
        let array = [(), (), (), (), (), ()];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert!(instance.iter().eq(array.iter()));
    }

    #[test]
    fn iter_mut_normal_type() {
        let mut array = [0, 1, 2, 3, 4, 5];
        let mut instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert!(instance.iter_mut().eq(array.iter_mut()));
    }

    #[test]
    fn iter_mut_zero_size_type() {
        let mut array = [(), (), (), (), (), ()];
        let mut instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert!(instance.iter_mut().eq(array.iter_mut()));
    }

    #[test]
    fn first_normal_type() {
        let array = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert_eq!(instance.first().unwrap(), array.first().unwrap());
    }

    #[test]
    fn first_zero_size_type() {
        let array = [(), (), (), (), (), ()];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert_eq!(instance.first().unwrap(), array.first().unwrap());
    }

    #[test]
    fn last_normal_type() {
        let array = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };
        assert_eq!(instance.last().unwrap(), array.last().unwrap());
    }

    #[test]
    fn last_zero_size_type() {
        let array = [(), (), (), (), (), ()];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert_eq!(instance.last().unwrap(), array.last().unwrap());
    }

    #[test]
    fn index_normal_type() {
        let array = [0, 1, 2, 3,4,5];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        for (index, value) in array.iter().enumerate() {
            assert_eq!(instance[index], *value);
        }
    }

    #[test]
    fn index_zero_size_type() {
        let array = [(), (), (), (), (), ()];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        for (index, value) in array.iter().enumerate() {
            assert_eq!(instance[index], *value);
        }
    }

    #[test]
    fn index_mut_normal_type() {
        let mut array = [0, 1, 2, 3,4,5];
        let mut instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        for (index, value) in array.iter().enumerate() {
            assert_eq!(instance[index], *value);

            instance[index] = 0;

            assert_eq!(instance[index], 0);
        }
    }

    #[test]
    fn index_mut_zero_size_type() {
        let mut array = [(), (), (), (),(),()];
        let mut instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        for (index, value) in array.iter().enumerate() {
            assert_eq!(instance[index], *value);

            instance[index] = ();

            assert_eq!(instance[index], ());
        }
    }

    #[test]
    fn deref_normal_type() {
        let array = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        use std::ops::Deref;
        assert_eq!(instance.deref(), array.as_slice());
    }

    #[test]
    fn deref_zero_size_type() {
        let array = [(), (), (), (), (), ()];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        use std::ops::Deref;
        assert_eq!(instance.deref(), array.as_slice());
    }

    #[test]
    fn deref_mut() {
        let mut array = [0, 1, 2, 3];
        let mut instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        use std::ops::DerefMut;
        assert_eq!(instance.deref_mut(), array.as_slice());
    }

    #[test]
    fn eq() {
        let array = [0, 1, 2, 3];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        let other = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert_eq!(instance, other);
    }

    #[test]
    fn ne() {
        let array = [0, 1, 2, 3];
        let instance = {
            let ptr = array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        let other_array = [4, 5, 6, 7];
        let other = {
            let ptr = other_array.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, other_array.len()) }
        };

        assert_ne!(instance, other);
    }
}
