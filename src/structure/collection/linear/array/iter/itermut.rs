//! Implementation of [`IterMut`].

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
    /// use rust::structure::collection::linear::array::iter::IterMut;
    ///
    /// let mut underlying = [0, 1, 2, 3, 4, 5];
    /// let ptr = std::ptr::NonNull::new(underlying.as_mut_ptr()).unwrap();
    /// let iter = unsafe { IterMut::new(ptr, underlying.len()) };
    ///
    /// assert!(underlying.iter().eq(iter));
    /// ```
    pub unsafe fn new(ptr: std::ptr::NonNull<T>, len: usize) -> Self {
        Self {
            next: ptr,
            end: super::end_of(ptr, len),
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> std::iter::Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY:
        // * valid (current, sentinel) pointer pair.
        // * `ptr` points to initialized element.
        unsafe { super::next(&mut self.next, self.end).map(|mut ptr| ptr.as_mut()) }
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

impl<'a, T: 'a> std::iter::ExactSizeIterator for IterMut<'a, T> {}

impl<'a, T: 'a> std::iter::DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        // SAFETY:
        // * valid (current, sentinel) pointer pair.
        // * `ptr` points to initialized element.
        unsafe { super::next_back(self.next, &mut self.end).map(|mut ptr| ptr.as_mut()) }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn size_hint_for_normal_types() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { IterMut::new(ptr, underlying.len()) }
        };

        assert_eq!(underlying.len(), instance.size_hint().0);
        assert_eq!(underlying.len(), instance.size_hint().1.unwrap());
    }

    #[test]
    fn size_hint_for_zero_size_types() {
        let underlying = [(), (), (), (), (), ()];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { IterMut::new(ptr, underlying.len()) }
        };

        assert_eq!(underlying.len(), instance.size_hint().0);
        assert_eq!(underlying.len(), instance.size_hint().1.unwrap());
    }

    #[test]
    fn len_for_normal_types() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { IterMut::new(ptr, underlying.len()) }
        };

        assert_eq!(underlying.len(), instance.len());
    }

    #[test]
    fn len_for_zero_size_types() {
        let underlying = [(), (), (), (), (), ()];
        let instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { IterMut::new(ptr, underlying.len()) }
        };

        assert_eq!(underlying.len(), instance.len());
    }

    #[test]
    fn next_normal_type() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let mut instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { IterMut::new(ptr, underlying.len()) }
        };

        assert!(underlying.iter().eq(instance));
    }

    #[test]
    fn next_zero_size_type() {
        let underlying = [(), (), (), (), (), ()];
        let mut instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { IterMut::new(ptr, underlying.len()) }
        };

        assert!(underlying.iter().eq(instance));
    }

    #[test]
    fn next_back_normal_type() {
        let underlying = [0, 1, 2, 3, 4, 5];
        let mut instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { IterMut::new(ptr, underlying.len()) }
        };

        assert!(underlying.iter().rev().eq(instance.rev()));
    }

    #[test]
    fn next_back_zero_size_type() {
        let underlying = [(), (), (), (), (), ()];
        let mut instance = {
            let ptr = underlying.as_ptr().cast_mut();
            let ptr = unsafe { std::ptr::NonNull::new_unchecked(ptr) };
            unsafe { IterMut::new(ptr, underlying.len()) }
        };

        assert!(underlying.iter().rev().eq(instance.rev()));
    }
}
