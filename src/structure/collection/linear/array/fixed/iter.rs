//! Iterators for [`Fixed`].

use super::Fixed;

/// By-value [`Iterator`] over a [`Fixed`].
pub struct IntoIter<T> {
    /// pointer to the hypotheical next element.
    next: *mut T,

    /// pointer to a sentinal end value.
    end: *mut T,
}

impl<T> IntoIter<T> {
    /// Construct an [`IntoIter`] for some [`Fixed`].
    fn new<const N: usize>(mut array: Fixed<T, N>) -> Self {
        Self {
            next: array.data.as_mut_ptr(),
            end: array.data.as_mut_ptr().wrapping_add(N),
        }
    }
}

impl<T> std::ops::Drop for IntoIter<T> {
    fn drop(&mut self) {
        while self.next != self.end {
            // SAFETY:
            // * owns underlying array => valid for reads and writes
            // * `wrapping_add` => pointer is properly aligned
            // * underlying array exists => pointer is non-null
            // * element has no yet been yeilded => valid to drop
            unsafe {
                std::ptr::drop_in_place(self.next);
            }
        }
    }
}

impl<T> std::iter::Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next != self.end {
            // SAFETY:
            // * input array exists => non-null pointer
            // * `wrapping_add` => pointer is aligned
            // * next != end => pointing to initalized value
            let next = unsafe { std::ptr::read(self.next) };
            self.next = self.next.wrapping_add(1);
            Some(next)
        } else {
            None
        }
    }
}

impl<'a, T: 'a, const N: usize> std::iter::IntoIterator for Fixed<T, N> {
    type Item = T;

    type IntoIter = IntoIter<T>;

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
