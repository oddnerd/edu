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
pub struct Dope<'a, T: 'a> {
    /// Pointer to the start of the array.
    data: std::ptr::NonNull<T>,

    /// Number of elements within the array.
    len: usize,

    /// Bind lifetime to underlying memory buffer.
    lifetime: std::marker::PhantomData<&'a mut T>,
}

impl<'a, T: 'a> Dope<'a, T> {
    /// Construct from a pointer to the start of a memory buffer and the length
    /// of that buffer in elements of `T`.
    ///
    /// # SAFETY:
    /// * `data` must not be null.
    /// * `data` must have an address aligned for access to `T`.
    /// * `data` must point to one contigious allocated object.
    /// * `data` must point to `len` consecutive initialized instances of `T`.
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
    pub unsafe fn new(data: std::ptr::NonNull<T>, len: usize) -> Self {
        Self {
            data,
            len,
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> Collection<'a> for Dope<'a, T> {
    type Element = T;

    fn count(&self) -> usize {
        self.len
    }
}

/// By-value [`Iterator`] over a [`Dope`].
///
/// Note that because [`Dope`] is inherently non-owning over the memory buffer
/// it spans, therefore the values this yields are themselves references.
pub struct IntoIter<'a, T: 'a> {
    /// ownership of the values.
    data: Dope<'a, T>,

    /// elements within this range have yet to be yielded.
    next: std::ops::Range<std::ptr::NonNull<T>>,
}

impl<'a, T: 'a> IntoIter<'a, T> {
    /// Construct from a [`Dope`].
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dope;
    /// use rust::structure::collection::linear::array::dope::IntoIter;
    ///
    /// let mut underlying = [0, 1, 2, 3, 4, 5];
    /// let ptr = std::ptr::NonNull::new(underlying.as_mut_ptr()).unwrap();
    /// let dope = unsafe { Dope::new(ptr, underlying.len()) };
    /// let iter = IntoIter::new(dope);
    ///
    /// assert!(underlying.iter().eq(iter));
    /// ```
    pub fn new(dope: Dope<'a, T>) -> Self {
        let mut tmp = Self {
            data: dope,

            // careful to use pointers to the member and not the parameter.
            next: std::ptr::NonNull::dangling()..std::ptr::NonNull::dangling(),
        };

        // SAFETY: `wrapping_add` will maintain the non-null requirement.
        unsafe {
            let start = tmp.data.data;

            let end = std::ptr::NonNull::new_unchecked(start.as_ptr().wrapping_add(tmp.data.len));

            tmp.next = start..end;
        }

        tmp
    }
}

impl<'a, T: 'a> std::iter::Iterator for IntoIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next.start != self.next.end {
            // SAFETY:
            // * `wrapping_add` => pointer is aligned.
            // * next != end => pointing to initialized value.
            // * lifetime bound to input object => valid lifetime to return.
            let current = unsafe { self.next.start.as_ref() };

            // SAFETY: `wrapping_add` will maintain the non-null requirement.
            self.next.start = unsafe {
                let next = self.next.start.as_ptr().wrapping_add(1);

                std::ptr::NonNull::new_unchecked(next)
            };

            Some(current)
        } else {
            None
        }
    }
}

impl<'a, T: 'a> std::iter::IntoIterator for Dope<'a, T> {
    type Item = &'a T;

    type IntoIter = IntoIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter::new(self)
    }
}

impl<'a, T: 'a> Linear<'a> for Dope<'a, T> {
    fn iter(&self) -> impl std::iter::Iterator<Item = &'a Self::Element> {
        // SAFETY: requirements are already enforced by the constructor.
        unsafe { super::iter::Iter::new(self.data, self.len) }
    }

    fn iter_mut(&mut self) -> impl std::iter::Iterator<Item = &'a mut Self::Element> {
        // SAFETY: requirements are already enforced by the constructor.
        unsafe { super::iter::IterMut::new(self.data, self.len) }
    }

    fn first(&self) -> Option<&Self::Element> {
        if self.len > 0 {
            // SAFETY:
            // * constructor contract => `self.data` is aligned
            // * constructor contract => `self.data` is dereferenceable.
            // * constructor contract => pointed to `T` is initialized.
            // * constructor contract => valid lifetime to return.
            unsafe { Some( self.data.as_ref() ) }
        } else {
            None
        }
    }

    fn last(&self) -> Option<&Self::Element> {
        if self.len > 0 {
            let ptr = self.data.as_ptr();

            // SAFETY: remains within the one underlying allocated object.
            let ptr = unsafe { ptr.add(self.len - 1) };

            // SAFETY:
            // * constructor contract => `ptr` is aligned
            // * constructor contract => `ptr` is dereferenceable.
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
        assert!(index < self.len);
        // SAFETY:
        // * `data` is [`NonNull`] => pointer will be non-null.
        // * index is within bounds => `add` stays within bounds.
        // * `add` => pointer is aligned.
        // * underlying object is initialized => points to initialized `T`.
        // * lifetime bound to input object => valid lifetime to return.
        unsafe { &*self.data.as_ptr().add(index) }
    }
}

impl<'a, T: 'a> std::ops::IndexMut<usize> for Dope<'a, T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert!(index < self.len);
        // SAFETY:
        // * `data` is [`NonNull`] => pointer will be non-null.
        // * index is within bounds => `add` stays within bounds.
        // * `add` => pointer is aligned.
        // * underlying object is initialized => points to initialized `T`.
        // * lifetime bound to input object => valid lifetime to return.
        unsafe { &mut *self.data.as_ptr().add(index) }
    }
}

impl<'a, T: 'a> std::ops::Deref for Dope<'a, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // SAFETY:
        // * `data` is aligned => pointer is aligned.
        // * `data` is initialized => every element is initialized.
        // * `data` is one object => slice is over one allocated object.
        unsafe { std::slice::from_raw_parts(self.data.as_ptr(), self.len) }
    }
}

impl<'a, T: 'a> std::ops::DerefMut for Dope<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY:
        // * `data` is aligned => pointer is aligned.
        // * `data` is initialized => every element is initialized.
        // * `data` is one object => slice is over one allocated object.
        unsafe { std::slice::from_raw_parts_mut(self.data.as_ptr(), self.len) }
    }
}

impl<'a, T: 'a> Array<'a> for Dope<'a, T> {}

impl<'a, T: 'a + PartialEq> PartialEq for Dope<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<'a, T: 'a + Eq> std::cmp::Eq for Dope<'a, T> {}

impl<'a,T:'a + std::fmt::Debug> std::fmt::Debug for Dope<'a, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new() {
        let mut array = [0, 1, 2, 3];
        let instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert_eq!(instance.data.as_ptr(), array.as_mut_ptr());
        assert_eq!(instance.len, array.len());
    }

    #[test]
    fn count() {
        let mut array = [0, 1, 2, 3];
        let instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert_eq!(instance.len(), array.len());
    }

    #[test]
    fn into_iter() {
        let mut array = [0, 1, 2, 3];
        let instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert!(instance.into_iter().copied().eq(array.into_iter()));
    }

    #[test]
    fn iter() {
        let mut array = [0, 1, 2, 3];
        let instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert!(instance.iter().eq(array.iter()));
    }

    #[test]
    fn iter_mut() {
        let mut array = [0, 1, 2, 3];
        let mut instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert!(instance.iter_mut().eq(array.iter_mut()));
    }

    #[test]
    fn first() {
        let mut array = [0, 1, 2, 3];
        let mut instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert_eq!(*instance.first().unwrap(), instance[0]);
    }

    #[test]
    fn last() {
        let mut array = [0, 1, 2, 3];
        let mut instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert_eq!(*instance.last().unwrap(), instance[0]);
    }

    #[test]
    fn index() {
        let mut array = [0, 1, 2, 3];
        let instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert_eq!(instance[0], 0);
        assert_eq!(instance[1], 1);
        assert_eq!(instance[2], 2);
        assert_eq!(instance[3], 3);
    }

    #[test]
    fn index_mut() {
        let mut array = [0, 1, 2, 3];
        let mut instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        instance[0] = 4;
        instance[1] = 5;
        instance[2] = 6;
        instance[3] = 7;

        assert_eq!(instance[0], 4);
        assert_eq!(instance[1], 5);
        assert_eq!(instance[2], 6);
        assert_eq!(instance[3], 7);
    }

    #[test]
    fn deref() {
        let mut array = [0, 1, 2, 3];
        let instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        use std::ops::Deref;
        assert_eq!(*instance.deref(), *array.as_slice());
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
        assert_eq!(*instance.deref_mut(), *array.as_slice());
    }

    #[test]
    fn eq() {
        let mut array = [0, 1, 2, 3];
        let instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        let other = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        assert_eq!(instance, other);
    }

    #[test]
    fn ne() {
        let mut array = [0, 1, 2, 3];
        let instance = {
            let ptr = array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, array.len()) }
        };

        let mut other_array = [4,5,6,7];
        let other = {
            let ptr = other_array.as_mut_ptr();
            let ptr = std::ptr::NonNull::new(ptr).unwrap();
            unsafe { Dope::new(ptr, other_array.len()) }
        };

        assert_ne!(instance, other);
    }
}
