//! Iterators over contigious memory buffers of consecutive elements; arrays.


/// Immutable reference [`Iterator`] over an [`Array`]`.
pub struct Iter<'a, T: 'a> {
    /// pointer to the hypothetical next element.
    next: std::ptr::NonNull<T>,

    /// pointer to a sentinel value when elements are exhausted.
    end: std::ptr::NonNull<T>,

    /// constrain to lifetime of the underlying object.
    lifetime: std::marker::PhantomData<&'a T>,
}

impl<'a, T: 'a> Iter<'a, T> {
    /// Construct from a pointer to the start of a memory buffer and the length
    /// of that buffer in elements of `T`.
    ///
    /// # SAFETY:
    /// * `ptr` must not be null.
    /// * `ptr` must have an address aligned for access to `T`.
    /// * `ptr` must point to one contigious allocated object.
    /// * `ptr` must point to `len` consecutive initialized instances of `T`.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::iter::Iter;
    ///
    /// let mut underlying = [0, 1, 2, 3, 4, 5];
    /// let ptr = std::ptr::NonNull::new(underlying.as_mut_ptr()).unwrap();
    /// let iter = unsafe { Iter::new(ptr, underlying.len()) };
    ///
    /// assert!(underlying.iter().eq(iter));
    /// ```
    pub unsafe fn new(ptr: std::ptr::NonNull<T>, len: usize) -> Self {
        Self {
            next: ptr,
            // SAFETY: `wrapping_add` will maintain the non-null requirement.
            end: unsafe {
                let ptr = ptr.as_ptr();
                let sentinel = ptr.wrapping_add(len);
                std::ptr::NonNull::new_unchecked(sentinel)
            },
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> std::iter::Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next != self.end {
            // SAFETY:
            // * `wrapping_add` => pointer is aligned.
            // * next != end => pointing to initialized value.
            // * lifetime bound to input object => valid lifetime to return.
            let current = unsafe { self.next.as_ref() };

            // SAFETY: `wrapping_add` will maintain the non-null requirement.
            self.next = unsafe {
                let ptr = self.next.as_ptr();
                let next = ptr.wrapping_add(1);
                std::ptr::NonNull::new_unchecked(next)
            };

            Some(current)
        } else {
            None
        }
    }
}

/// Mutable reference [`Iterator`] over an [`Array`].
pub struct IterMut<'a, T: 'a> {
    /// pointer to the hypothetical next element.
    next: std::ptr::NonNull<T>,

    /// pointer to a sentinel value when elements are exhausted.
    end: std::ptr::NonNull<T>,

    /// constrain to lifetime of the underlying object.
    lifetime: std::marker::PhantomData<&'a T>,
}

impl<'a, T: 'a> IterMut<'a, T> {
    /// Construct from a pointer to the start of a memory buffer and the length
    /// of that buffer in elements of `T`.
    ///
    /// # SAFETY:
    /// * `ptr` must not be null.
    /// * `ptr` must have an address aligned for access to `T`.
    /// * `ptr` must point to one contigious allocated object.
    /// * `ptr` must point to `len` consecutive initialized instances of `T`.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::iter::Iter;
    ///
    /// let mut underlying = [0, 1, 2, 3, 4, 5];
    /// let ptr = std::ptr::NonNull::new(underlying.as_mut_ptr()).unwrap();
    /// let iter = unsafe { Iter::new(ptr, underlying.len()) };
    ///
    /// assert!(underlying.iter().eq(iter));
    /// ```
    pub unsafe fn new(ptr: std::ptr::NonNull<T>, len: usize) -> Self {
        Self {
            next: ptr,
            // SAFETY: `wrapping_add` will maintain the non-null requirement.
            end: unsafe {
                let ptr = ptr.as_ptr();
                let sentinel = ptr.wrapping_add(len);
                std::ptr::NonNull::new_unchecked(sentinel)
            },
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> std::iter::Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next != self.end {
            // SAFETY:
            // * `wrapping_add` => pointer is aligned.
            // * next != end => pointing to initialized value.
            // * lifetime bound to input object => valid lifetime to return.
            let current = unsafe { self.next.as_mut() };

            // SAFETY: `wrapping_add` will maintain the non-null requirement.
            self.next = unsafe {
                let ptr = self.next.as_ptr();
                let next = ptr.wrapping_add(1);
                std::ptr::NonNull::new_unchecked(next)
            };

            Some(current)
        } else {
            None
        }
    }
}
