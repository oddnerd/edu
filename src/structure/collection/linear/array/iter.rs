//! Iterators over contigious memory buffers of consecutive elements; [`super::Array`].

mod iter;
pub use iter::Iter;

mod itermut;
pub use itermut::IterMut;

/// Obtain a sentinel value pointer for an array at `ptr` with `len` elements.
///
/// # Safety
/// `ptr` must point to `len` consecutive initialized instanced of `T` within
/// one allocated object
#[inline]
unsafe fn end_of<T>(ptr: std::ptr::NonNull<T>, len: usize) -> std::ptr::NonNull<T> {
    if std::mem::size_of::<T>() == 0 {
        // treat the pointer as any other integer counter.
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

/// Implement [`Iterator::next()`] via a (current, sentinel) pointer pair.
///
/// # Safety
/// * `next` and `end` must be aligned for `T`.
/// * `next` and `end` must point to the same allocated object.
/// * `end` must be some positive offset from `next`.
#[inline]
unsafe fn next<T>(
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

/// Implement [`DoubleEndedIterator::next_back()`] via a (current, sentinel)
/// pointer pair.
///
/// # Safety
/// * `next` and `end` must be aligned for `T`.
/// * `next` and `end` must point to the same allocated object.
/// * `end` must be some positive offset from `next`.
#[inline]
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
