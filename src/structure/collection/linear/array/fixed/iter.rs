//! Iterators for [`Fixed`].

use super::Fixed;

/// By-value [`Iterator`] over a [`Fixed`].
pub struct IntoIter<T, const N: usize> {
    /// ownership of the underlying array.
    data: [std::mem::ManuallyDrop<T>; N],

    /// elements within the range have yet to be yeilded.
    next: std::ops::Range<std::ptr::NonNull<std::mem::ManuallyDrop<T>>>,
}

impl<T, const N: usize> IntoIter<T, N> {
    /// Construct an [`IntoIter`] for some [`Fixed`].
    fn new(mut array: Fixed<T, N>) -> Self {
        let mut tmp = Self {
            // SAFETY:
            // * ManuallyDrop<T> has same size as T => arrays have same size
            // * ManuallyDrop<T> has same alignment as T => elements aligned
            data: unsafe {
                array
                    .data
                    .as_mut_ptr()
                    .cast::<[std::mem::ManuallyDrop<T>; N]>()
                    .read()
            },

            // careful to use pointers to the member and not the parameter.
            next: std::ptr::NonNull::dangling()..std::ptr::NonNull::dangling(),
        };

        // SAFETY: the array exists => pointers to it can't be null
        unsafe {
            let ptr = tmp.data.as_mut_ptr();

            let start = std::ptr::NonNull::new_unchecked(ptr);

            let end = std::ptr::NonNull::new_unchecked(ptr.wrapping_add(N));

            tmp.next = start..end;
        }

        tmp
    }
}

impl<T, const N: usize> std::ops::Drop for IntoIter<T, N> {
    fn drop(&mut self) {
        while self.next.start != self.next.end {
            // SAFETY:
            // * owns underlying array => valid for reads and writes
            // * `wrapping_add` => pointer is properly aligned
            // * underlying array exists => pointer is non-null
            // * element has no yet been yeilded => valid to drop
            unsafe {
                std::ptr::drop_in_place(self.next.start.as_ptr());
            }

            let next = self.next.start.as_ptr().wrapping_add(1);

            // SAFETY: the pointer wasn't null before so it still won't be.
            let next = unsafe { std::ptr::NonNull::new_unchecked(next) };

            self.next.start = next;
        }
    }
}

impl<T, const N: usize> std::iter::Iterator for IntoIter<T, N> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next.start != self.next.end {
            // SAFETY:
            // * input array exists => non-null pointer
            // * `wrapping_add` => pointer is aligned
            // * within bounds => pointing to initalized value
            let current = unsafe {
                let copy = self.next.start.as_ptr().read();
                std::mem::ManuallyDrop::into_inner(copy)
            };

            let next = self.next.start.as_ptr().wrapping_add(1);

            // SAFETY: the pointer wasn't null before so it still won't be.
            let next = unsafe { std::ptr::NonNull::new_unchecked(next) };

            self.next.start = next;

            Some(current)
        } else {
            None
        }
    }
}

impl<'a, T: 'a, const N: usize> std::iter::IntoIterator for Fixed<T, N> {
    type Item = T;

    type IntoIter = IntoIter<T, N>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter::new(self)
    }
}

/// Immutable reference [`Iterator`] over a [`Fixed`].
pub struct Iter<'a, T: 'a> {
    /// pointer to the hypotheical next element.
    next: *const T,

    /// pointer to a sentinal end value.
    end: *const T,

    /// constrain to lifetime of the underlying [`Fixed`].
    lifetime: std::marker::PhantomData<&'a T>,
}

impl<'a, T: 'a> Iter<'a, T> {
    /// Construct an [`Iter`] for some [`Fixed`].
    pub fn new<const N: usize>(array: &Fixed<T, N>) -> Self {
        Self {
            next: array.data.as_ptr(),
            end: array.data.as_ptr().wrapping_add(N),
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T> std::iter::Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next != self.end {
            // SAFETY:
            // * input array exists => non-null pointer
            // * `wrapping_add` => pointer is aligned
            // * next != end => pointing to initalized value
            // * lifetime 'a bound to input array => valid lifetime to return
            let element = unsafe { &*self.next };
            self.next = self.next.wrapping_add(1);
            Some(element)
        } else {
            None
        }
    }
}

/// Immutable reference [`Iterator`] over a [`Fixed`].
pub struct IterMut<'a, T: 'a> {
    /// pointer to the hypotheical next element.
    next: *mut T,

    /// pointer to a sentinal end value.
    end: *mut T,

    /// constrain to lifetime of the underlying [`Fixed`].
    lifetime: std::marker::PhantomData<&'a mut T>,
}

impl<'a, T: 'a> IterMut<'a, T> {
    /// Construct an [`IterMut`] for some [`Fixed`].
    pub fn new<const N: usize>(array: &mut Fixed<T, N>) -> Self {
        Self {
            next: array.data.as_mut_ptr(),
            end: array.data.as_mut_ptr().wrapping_add(N),
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T> std::iter::Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next != self.end {
            // SAFETY:
            // * input array exists => non-null pointer
            // * `wrapping_add` => pointer is aligned
            // * next != end => pointing to initalized value
            // * lifetime 'a bound to input array => valid lifetime to return
            let element = unsafe { &mut *self.next };
            self.next = self.next.wrapping_add(1);
            Some(element)
        } else {
            None
        }
    }
}
