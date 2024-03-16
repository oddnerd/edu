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
#[derive(Clone, Copy, Hash)]
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
        use std::ops::Not;
        if self.is_empty().not() {
            // SAFETY:
            // * constructor contract => pointed to `T` is initialized.
            // * constructor contract => valid lifetime to return.
            unsafe { Some(self.ptr.as_ref()) }
        } else {
            None
        }
    }

    fn last(&self) -> Option<&Self::Element> {
        use std::ops::Not;
        if self.is_empty().not() {
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

impl<'a, T: 'a + PartialEq> std::cmp::PartialEq for Dope<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        *self.as_slice() == *other.as_slice()
    }
}

impl<'a, T: 'a + Eq> std::cmp::Eq for Dope<'a, T> {}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new_initializes_member_variables() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance.ptr.as_ptr(), underlying.as_ptr().cast_mut());
        assert_eq!(instance.count, underlying.len());
    }

    #[test]
    fn from_slice_initializes_member_variables() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let instance = Dope::from(underlying.as_slice());

        assert_eq!(instance.ptr.as_ptr(), underlying.as_ptr().cast_mut());
        assert_eq!(instance.count, underlying.len());
    }

    #[test]
    fn count_for_normal_types_is_exact_element_count() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance.count(), underlying.len());
    }

    #[test]
    fn count_for_zero_size_types_is_constructed_count() {
        let underlying = [(), (), (), (), (), ()];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance.count(), underlying.len());
    }

    #[test]
    fn into_iter_yields_element_count_for_normal_types() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance.into_iter().count(), underlying.len());
    }

    #[test]
    fn into_iter_yields_element_count_for_zero_size_types() {
        let underlying = [(), (), (), (), (), ()];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance.into_iter().count(), underlying.len());
    }

    #[test]
    fn into_iter_yields_elements() {
        let underlying = [0, 1, 2, 3, 4, 5];

        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert!(instance.into_iter().eq(underlying.as_slice()));
    }

    #[test]
    fn iter_yields_element_count_for_normal_types() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance.iter().count(), underlying.len());
    }

    #[test]
    fn iter_yields_element_count_for_zero_size_types() {
        let underlying = [(), (), (), (), (), ()];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance.iter().count(), underlying.len());
    }

    #[test]
    fn iter_yields_elements() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert!(instance.iter().eq(underlying.as_slice()));
    }

    #[test]
    fn iter_mut_yields_element_count_for_normal_types() {
        let mut underlying = [0, 1, 2, 3, 4, 5];
        let mut instance = {
            let ptr = underlying.as_mut_ptr();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance.iter_mut().count(), underlying.len());
    }

    #[test]
    fn iter_mut_yields_element_count_for_zero_size_types() {
        let mut underlying = [(), (), (), (), (), ()];
        let mut instance = {
            let ptr = underlying.as_mut_ptr();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance.iter_mut().count(), underlying.len());
    }

    #[test]
    fn iter_mut_yields_elements() {
        let mut underlying = [0, 1, 2, 3, 4, 5];
        let mut instance = {
            let ptr = underlying.as_mut_ptr();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert!(instance.iter_mut().eq(underlying.as_slice()));
    }

    #[test]
    fn first_yields_none_when_empty() {
        let underlying: [(); 0] = [];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance.first(), None);
    }

    #[test]
    fn first_yields_correct_element() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance.first(), underlying.first());
    }

    #[test]
    fn first_mut_yields_none_when_empty() {
        let underlying: [(); 0] = [];
        let mut instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance.first_mut(), None);
    }

    #[test]
    fn last_yields_none_when_empty() {
        let underlying: [(); 0] = [];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance.last(), None);
    }

    #[test]
    fn last_yields_correct_element() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance.last(), underlying.last());
    }

    #[test]
    fn index_yields_correct_element() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        for (index, value) in underlying.iter().enumerate() {
            use std::ops::Index;
            assert_eq!(instance.index(index), value);
        }
    }

    #[test]
    #[should_panic]
    fn index_panics_when_out_of_bounds() {
        let underlying: [(); 0] = [];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        use std::ops::Index;
        instance.index(0);
    }

    #[test]
    fn index_mut_yields_correct_element() {
        let mut underlying = [0, 1, 2, 3, 4, 5];
        let mut instance = {
            let ptr = underlying.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        for (index, value) in underlying.iter_mut().enumerate() {
            use std::ops::IndexMut;
            assert_eq!(instance.index_mut(index), value);
        }
    }

    #[test]
    #[should_panic]
    fn index_mut_panics_when_out_of_bounds() {
        let underlying: [(); 0] = [];
        let mut instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        use std::ops::IndexMut;
        instance.index_mut(0);
    }

    #[test]
    fn deref_to_valid_slice() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        use std::ops::Deref;
        assert_eq!(instance.deref(), underlying.as_slice());
    }

    #[test]
    fn deref_mut_to_valid_slice() {
        let mut underlying = [0, 1, 2, 3, 4, 5];
        let mut instance = {
            let ptr = underlying.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        use std::ops::DerefMut;
        assert_eq!(instance.deref_mut(), underlying.as_mut_slice());
    }

    #[test]
    fn eq_for_same_underlying() {
        let underlying = [0, 1, 2, 3, 4, 5];

        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        let other = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance, other);
    }

    #[test]
    fn eq_for_same_elements() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        let underlying = [0, 1, 2, 3, 4, 5];
        let other = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_eq!(instance, other);
    }

    #[test]
    fn ne_for_different_count() {
        let underlying = [0, 1, 2, 3, 4, 5];

        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        let other = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len() - 1) }
        };

        assert_ne!(instance, other);
    }

    #[test]
    fn ne_for_different_elements() {
        let underlying = [0];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        let underlying = [1];
        let other = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        assert_ne!(instance, other);
    }

    #[test]
    fn clone_is_eq() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let original = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, underlying.len()) }
        };

        let clone = original.clone();

        assert_eq!(clone, original);
    }
}
