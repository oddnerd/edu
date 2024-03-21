//! Implementation of [`Dope`].

use super::Array;
use super::Collection;
use super::Linear;

/// Lightweight access to a contigious buffer of memory.
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
    /// * Cannot use this object to modify immutable underlying memory.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory for the result.
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
    /// assert!(dope.iter().eq(underlying));
    /// ```
    pub unsafe fn new(ptr: std::ptr::NonNull<T>, count: usize) -> Self {
        Self {
            ptr,
            count,
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> std::convert::From<&'a mut [T]> for Dope<'a, T> {
    /// Construct from an existing [`slice`].
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut underlying = [0, 1, 2, 3, 4, 5];
    /// let dope = unsafe { Dope::from(underlying.as_mut_slice()) };
    ///
    /// assert!(dope.iter().eq(underlying));
    /// ```
    fn from(slice: &'a mut [T]) -> Self {
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

    /// Query how many elements are referenced to/contained.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let underlying = [0, 1, 2, 3, 4, 5];
    /// let dope = unsafe { Dope::from(underlying.as_mut_slice()) };
    ///
    /// assert_eq!(dope.count(), underlying.len());
    /// ```
    fn count(&self) -> usize {
        self.count
    }
}

impl<'a, T: 'a> std::ops::Index<usize> for Dope<'a, T> {
    type Output = T;

    /// Query the element `index` positions from the start.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut underlying = [0, 1, 2, 3, 4, 5];
    /// let ptr = std::ptr::NonNull::new(underlying.as_mut_ptr()).unwrap();
    /// let dope = unsafe { Dope::new(ptr, underlying.len()) };
    ///
    /// for index in 0..underlying.len() {
    ///     assert_eq!(dope.index(index), underlying.index(index));
    /// }
    /// ```
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
    /// Obtain a reference to the element `index` positions from the start.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut underlying = [0, 1, 2, 3, 4, 5];
    /// let ptr = std::ptr::NonNull::new(underlying.as_mut_ptr()).unwrap();
    /// let dope = unsafe { Dope::new(ptr, underlying.len()) };
    ///
    /// for index in 0..underlying.len() {
    ///     assert_eq!(dope.index_mut(index), underlying.index_mut(index));
    /// }
    /// ```
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

impl<'a, T: 'a> Linear<'a> for Dope<'a, T> {
    /// Immutably iterate the elements in order.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let underlying = [0, 1, 2, 3, 4, 5];
    /// let dope = unsafe { Dope::from(underlying.as_mut_slice()) };
    ///
    /// for (actual, expected) in dope.iter().zip(underlying.iter()) {
    ///     assert_eq!(actual, expected);
    /// }
    /// ```
    fn iter(&self) -> impl std::iter::Iterator<Item = &'a Self::Element> {
        unsafe { super::Iter::new(self.ptr, self.count) }
    }

    /// Mutably iterate the elements in order.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let underlying = [0, 1, 2, 3, 4, 5];
    /// let dope = unsafe { Dope::from(underlying.as_mut_slice()) };
    ///
    /// for (actual, expected) in dope.iter_mut().zip(underlying.iter_mut()) {
    ///     assert_eq!(actual, expected);
    /// }
    /// ```
    fn iter_mut(&mut self) -> impl std::iter::Iterator<Item = &'a mut Self::Element> {
        unsafe { super::IterMut::new(self.ptr, self.count) }
    }
}

impl<'a, T: 'a> Array<'a> for Dope<'a, T> {
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
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let underlying = [0, 1, 2, 3, 4, 5];
    /// let dope = unsafe { Dope::from(underlying.as_mut_slice()) };
    ///
    /// assert_eq!(dope.as_ptr(), underlying.as_ptr());
    /// ```
    unsafe fn as_ptr(&self) -> *const Self::Element {
        self.ptr.as_ptr().cast_const()
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
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let underlying = [0, 1, 2, 3, 4, 5];
    /// let dope = unsafe { Dope::from(underlying.as_mut_slice()) };
    ///
    /// assert_eq!(dope.as_mut_ptr(), underlying.as_mut_ptr());
    /// ```
    unsafe fn as_mut_ptr(&mut self) -> *mut Self::Element {
        self.ptr.as_ptr()
    }
}

impl<'a, T: 'a + std::fmt::Debug> std::fmt::Debug for Dope<'a, T> {
    /// List the elements referenced to/contained.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let underlying = [0, 1, 2, 3, 4, 5];
    /// let dope = unsafe { Dope::from(underlying.as_mut_slice()) };
    ///
    /// assert_eq!(format!("{dope:?}"), "[0, 1, 2, 3, 4, 5]");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<'a, T> std::fmt::Pointer for Dope<'a, T> {
    /// Display the underlying address pointed to.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let underlying = [0, 1, 2, 3, 4, 5];
    /// let dope = unsafe { Dope::from(underlying.as_mut_slice()) };
    ///
    /// assert_eq!(format!("{dope:P}"), format!("{:P}", underlying.as_ptr()));
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // SAFETY: the address of the pointer it read, not the pointer itself.
        std::fmt::Pointer::fmt(unsafe { &self.as_ptr() }, f)
    }
}

impl<'a, T: 'a + PartialEq> std::cmp::PartialEq for Dope<'a, T> {
    /// Query if the elements referenced to/contained are the same as `other`.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let underlying = [0, 1, 2, 3, 4, 5];
    /// let dope = unsafe { Dope::from(underlying.as_mut_slice()) };
    ///
    /// let underlying = underlying.clone();
    /// let other = unsafe { Dope::from(underlying.as_mut_slice()) };
    ///
    /// assert_eq!(dope, other);
    /// ```
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
        let mut underlying = [0, 1, 2, 3, 4, 5];
        let pointer = underlying.as_mut_ptr();

        let instance = Dope::from(underlying.as_mut_slice());

        assert_eq!(instance.ptr.as_ptr(), pointer);
        assert_eq!(instance.count, underlying.len());
    }

    #[test]
    fn count_for_normal_types_is_exact_element_count() {
        let mut underlying = [0, 1, 2, 3, 4, 5];
        let instance = Dope::from(underlying.as_mut_slice());

        assert_eq!(instance.count(), underlying.len());
    }

    #[test]
    fn count_for_zero_size_types_is_constructed_count() {
        let mut underlying = [(), (), (), (), (), ()];
        let instance = Dope::from(underlying.as_mut_slice());

        assert_eq!(instance.count(), underlying.len());
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
