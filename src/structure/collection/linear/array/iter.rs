//! Iterators over contigious memory buffers of consecutive elements; [`Array`].

/// Immutable reference [`Iterator`] over an [`Array`].
pub struct Iter<'a, T: 'a> {
    /// Pointer to the hypothetical next element.
    next: std::ptr::NonNull<T>,

    /// Pointer to a sentinel value when elements are exhausted.
    end: std::ptr::NonNull<T>,

    /// Constrain to lifetime of the underlying object.
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
            end: if std::mem::size_of::<T>() == 0 {
                // treat the pointer as any another integer counter.
                let next = ptr.as_ptr() as usize;
                let next = next.wrapping_add(len);
                let next = next as *mut T;

                // SAFETY: null-ness doesn't apply here.
                unsafe { std::ptr::NonNull::new_unchecked(next) }
            } else {
                // SAFETY: one byte past the end of the allocated object.
                let sentinel = unsafe { ptr.as_ptr().add(len) };

                // SAFETY: `add` will maintain the non-null requirement.
                unsafe { std::ptr::NonNull::new_unchecked(sentinel) }
            },
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> std::iter::Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next != self.end {
            if std::mem::size_of::<T>() == 0 {
                self.next = {
                    // treat the pointer as another integer type with counter.
                    let next = self.next.as_ptr() as usize;
                    let next = next.wrapping_add(1);
                    let next = next as *mut T;

                    // SAFETY: null-ness doesn't apply here.
                    unsafe { std::ptr::NonNull::new_unchecked(next) }
                };

                // SAFETY:
                // * pointer is aligned.
                // * pointer is non-null.
                // * zero-sized type makes this special-case `read` okay.
                return Some(unsafe { std::ptr::NonNull::<T>::dangling().as_ref() });
            }

            // SAFETY:
            // * `self.next != self.end` => pointing to initialized value.
            // * lifetime bound to input object => valid lifetime to return.
            let current = unsafe { self.next.as_ref() };

            self.next = {
                // SAFETY: either within the allocated object or one byte past.
                let next = unsafe { self.next.as_ptr().add(1) };

                // SAFETY: `add` will maintain the non-null requirement.
                unsafe { std::ptr::NonNull::new_unchecked(next) }
            };

            Some(current)
        } else {
            None
        }
    }
}

/// Mutable reference [`Iterator`] over an [`Array`].
pub struct IterMut<'a, T: 'a> {
    /// Pointer to the hypothetical next element.
    next: std::ptr::NonNull<T>,

    /// Pointer to a sentinel value when elements are exhausted.
    end: std::ptr::NonNull<T>,

    /// Constrain to lifetime of the underlying object.
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
            end: if std::mem::size_of::<T>() == 0 {
                // treat the pointer as any another integer counter.
                let next = ptr.as_ptr() as usize;
                let next = next.wrapping_add(len);
                let next = next as *mut T;

                // SAFETY: null-ness doesn't apply here.
                unsafe { std::ptr::NonNull::new_unchecked(next) }
            } else {
                // SAFETY: one byte past the end of the allocated object.
                let sentinel = unsafe { ptr.as_ptr().add(len) };

                // SAFETY: `add` will maintain the non-null requirement.
                unsafe { std::ptr::NonNull::new_unchecked(sentinel) }
            },
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> std::iter::Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next != self.end {
            if std::mem::size_of::<T>() == 0 {
                self.next = {
                    // treat the pointer as another integer type with counter.
                    let next = self.next.as_ptr() as usize;
                    let next = next.wrapping_add(1);
                    let next = next as *mut T;

                    // SAFETY: null-ness doesn't apply here.
                    unsafe { std::ptr::NonNull::new_unchecked(next) }
                };

                // SAFETY:
                // * pointer is aligned.
                // * pointer is non-null.
                // * zero-sized type makes this special-case `read` okay.
                return Some(unsafe { std::ptr::NonNull::<T>::dangling().as_mut() });
            }

            // SAFETY:
            // * `self.next != self.end` => pointing to initialized value.
            // * lifetime bound to input object => valid lifetime to return.
            let current = unsafe { self.next.as_mut() };

            self.next = {
                // SAFETY: either within the allocated object or one byte past.
                let next = unsafe { self.next.as_ptr().add(1) };

                // SAFETY: `add` will maintain the non-null requirement.
                unsafe { std::ptr::NonNull::new_unchecked(next) }
            };

            Some(current)
        } else {
            None
        }
    }
}
