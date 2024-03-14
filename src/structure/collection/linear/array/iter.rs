//! Iterators over contigious memory buffers of consecutive elements; [`super::Array`].

/// Immutable reference [`Iterator`] over an [`super::Array`].
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
    /// # Safety
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
            end: end_of(ptr, len),
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> std::iter::Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        next(&mut self.next, self.end).map(|ptr| unsafe { ptr.as_ref() })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if std::mem::size_of::<T>() == 0 {
            // treat the pointer as any another integer counter.
            let end = self.end.as_ptr() as usize;
            let start = self.next.as_ptr() as usize;
            let size = end.wrapping_sub(start);

            (size, Some(size))
        } else {
            // SAFETY:
            // * both pointers are derived from the same allocated object.
            // * `next` is within bounds whereas `end` is one byte past the end.
            // * both pointers are aligned for `T`.
            // * this does not rely on wrapping logic.
            let size = unsafe { self.end.as_ptr().offset_from(self.next.as_ptr()) } as usize;

            (size, Some(size))
        }
    }
}

impl<'a, T: 'a> std::iter::DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        next_back(self.next, &mut self.end).map(|ptr| unsafe { ptr.as_ref() })
    }
}

impl<'a, T: 'a> std::iter::ExactSizeIterator for Iter<'a, T> {}

/// Mutable reference [`Iterator`] over an [`super::Array`].
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
    /// # Safety
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
            end: end_of(ptr, len),
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> std::iter::Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        next(&mut self.next, self.end).map(|mut ptr| unsafe { ptr.as_mut() })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if std::mem::size_of::<T>() == 0 {
            // treat the pointer as any another integer counter.
            let end = self.end.as_ptr() as usize;
            let start = self.next.as_ptr() as usize;
            let size = end.wrapping_sub(start);

            (size, Some(size))
        } else {
            // SAFETY:
            // * both pointers are derived from the same allocated object.
            // * `next` is within bounds whereas `end` is one byte past the end.
            // * both pointers are aligned for `T`.
            // * this does not rely on wrapping logic.
            let size = unsafe { self.end.as_ptr().offset_from(self.next.as_ptr()) } as usize;

            (size, Some(size))
        }
    }
}

impl<'a, T: 'a> std::iter::DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        next_back(self.next, &mut self.end).map(|mut ptr| unsafe { ptr.as_mut() })
    }
}

impl<'a, T: 'a> std::iter::ExactSizeIterator for IterMut<'a, T> {}

fn end_of<T>(ptr: std::ptr::NonNull<T>, len: usize) -> std::ptr::NonNull<T> {
    if std::mem::size_of::<T>() == 0 {
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
    }
}

fn next<T>(
    next: &mut std::ptr::NonNull<T>,
    end: std::ptr::NonNull<T>,
) -> Option<std::ptr::NonNull<T>> {
    if *next != end {
        if std::mem::size_of::<T>() == 0 {
            *next = {
                // treat the pointer address as an integer counter.
                let next = next.as_ptr() as usize;
                let next = next.wrapping_add(1);
                let next = next as *mut T;

                // SAFETY: null-ness doesn't apply here.
                unsafe { std::ptr::NonNull::new_unchecked(next) }
            };

            // SAFETY:
            // * pointer is aligned.
            // * pointer is non-null.
            // * zero-sized type makes it safe to read from this special-case.
            Some(std::ptr::NonNull::<T>::dangling())
        } else {
            let current = *next;

            *next = {
                // SAFETY: either within the allocated object or one byte past.
                let next = unsafe { next.as_ptr().add(1) };

                // SAFETY: `add` will maintain the non-null requirement.
                unsafe { std::ptr::NonNull::new_unchecked(next) }
            };

            // SAFETY: `next != end` => pointing to initialized value.
            Some(current)
        }
    } else {
        None
    }
}

fn next_back<T>(
    next: std::ptr::NonNull<T>,
    end: &mut std::ptr::NonNull<T>,
) -> Option<std::ptr::NonNull<T>> {
    if next != *end {
        if std::mem::size_of::<T>() == 0 {
            *end = {
                // treat the pointer as another integer type with counter.
                let end = end.as_ptr() as usize;
                let end = end.wrapping_sub(1);
                let end = end as *mut T;

                // SAFETY: null-ness doesn't apply here.
                unsafe { std::ptr::NonNull::new_unchecked(end) }
            };

            // SAFETY:
            // * pointer is aligned.
            // * pointer is non-null.
            // * zero-sized type makes it safe to read from this special-case.
            Some(std::ptr::NonNull::<T>::dangling())
        } else {
            *end = {
                // SAFETY: greater than `next` so within the allocated object.
                let end = unsafe { end.as_ptr().sub(1) };

                // SAFETY: `sub` will maintain the non-null requirement.
                unsafe { std::ptr::NonNull::new_unchecked(end) }
            };

            // SAFETY: `next != end` => pointing to initialized value.
            Some(*end)
        }
    } else {
        None
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn iter() {
        // sized type.
        {
            let underlying = [0, 1, 2, 3, 4, 5];
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            let iter = unsafe { Iter::new(ptr, underlying.len()) };
            assert_eq!((underlying.len(), Some(underlying.len())), iter.size_hint());
            assert!(underlying.iter().eq(iter));
        }

        // zero-sized type.
        {
            let underlying = [(), (), (), (), (), ()];
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            let iter = unsafe { Iter::new(ptr, underlying.len()) };
            assert_eq!((underlying.len(), Some(underlying.len())), iter.size_hint());
            assert!(underlying.iter().eq(iter));
        }
    }

    #[test]
    fn iter_mut() {
        // sized type.
        {
            let mut underlying = [0, 1, 2, 3, 4, 5];
            let ptr = std::ptr::NonNull::new(underlying.as_mut_ptr()).unwrap();
            let iter = unsafe { IterMut::new(ptr, underlying.len()) };
            assert_eq!((underlying.len(), Some(underlying.len())), iter.size_hint());
            assert!(underlying.iter().eq(iter));
        }

        // zero-sized type.
        {
            let mut underlying = [(), (), (), (), (), ()];
            let ptr = std::ptr::NonNull::new(underlying.as_mut_ptr()).unwrap();
            let iter = unsafe { IterMut::new(ptr, underlying.len()) };
            assert_eq!((underlying.len(), Some(underlying.len())), iter.size_hint());
            assert!(underlying.iter().eq(iter));
        }
    }
}
