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
/// [`Dope`] is equivalent to Rust's slice ([`[]`]) or C++'s span (`std::span`)
/// and views (`std::string_view`).
pub struct Dope<'a, T: 'a> {
    data: *mut T,
    len: usize,
    lifetime: std::marker::PhantomData<&'a T>,
}

impl<'a, T: 'a> Dope<'a, T> {
    /// Construct from a pointer to the start of a memory buffer and the length
    /// of that buffer in elements of `T`.
    ///
    /// SAFETY:
    /// * `data` must have an address aligned for access to `T`.
    /// * `data` must point to one contigious allocated object.
    /// * `data` must point to `len` consecutive initialized instances of `T`.
    pub unsafe fn new(data: *mut T, len: usize) -> Self {
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
pub struct IntoIter<'a, T> {
    /// ownership of the values.
    data: Dope<'a, T>,

    /// elements within this range have yet to be yielded.
    next: std::ops::Range<std::ptr::NonNull<T>>,
}

impl<'a, T: 'a> IntoIter<'a, T> {
    /// Construct an [`IntoIter`] for some [`Fixed`].
    fn new(dope: Dope<'a, T>) -> Self {
        let mut tmp = Self {
            data: dope,

            // careful to use pointers to the member and not the parameter.
            next: std::ptr::NonNull::dangling()..std::ptr::NonNull::dangling(),
        };

        // SAFETY: `data` member exists => pointers to it can't be null
        unsafe {
            let ptr = tmp.data.data;

            let start = std::ptr::NonNull::new_unchecked(ptr);

            let end = std::ptr::NonNull::new_unchecked(ptr.wrapping_add(tmp.data.len));

            tmp.next = start..end;
        }

        tmp
    }
}

impl<'a, T: 'a> std::iter::Iterator for IntoIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next.start != self.next.end {
            // SAFETY: references are bounded by the lifetime of the [`Dope`]
            let current = unsafe { self.next.start.as_ref() };

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

impl<'a, T: 'a> std::iter::IntoIterator for Dope<'a, T> {
    type Item = &'a T;

    type IntoIter = IntoIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter::new(self)
    }
}

/// Immutable reference [`Iterator`] over a [`Dope`].
pub struct Iter<'a, T: 'a> {
    /// pointer to the hypotheical next element.
    next: *const T,

    /// pointer to a sentinal end value.
    end: *const T,

    /// constrain to lifetime of the underlying [`Dope`].
    lifetime: std::marker::PhantomData<&'a T>,
}

impl<'a, T: 'a> Iter<'a, T> {
    /// Construct an [`Iter`] for some [`Dope`].
    pub fn new(dope: &Dope<'a, T>) -> Self {
        Self {
            next: dope.data,
            end: dope.data.wrapping_add(dope.len),
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> std::iter::Iterator for Iter<'a, T> {
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

/// Immutable reference [`Iterator`] over a [`Dope`].
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
    pub fn new(dope: &mut Dope<'a, T>) -> Self {
        Self {
            next: dope.data,
            end: dope.data.wrapping_add(dope.len),
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> std::iter::Iterator for IterMut<'a, T> {
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

impl<'a, T: 'a> Linear<'a> for Dope<'a, T> {
    fn iter(&self) -> impl std::iter::Iterator<Item = &'a Self::Element> {
        Iter::new(self)
    }

    fn iter_mut(&mut self) -> impl std::iter::Iterator<Item = &'a mut Self::Element> {
        IterMut::new(self)
    }
}

impl<'a, T: 'a> std::ops::Index<usize> for Dope<'a, T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < self.len);
        // SAFETY:
        // * index is within bounds => the pointer stays within bounds
        // * `add` in alignments of T => properly aligned pointer
        // * underlying array exists => points to initalized T
        unsafe { &*self.data.add(index) }
    }
}

impl<'a, T: 'a> std::ops::IndexMut<usize> for Dope<'a, T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert!(index < self.len);
        // SAFETY:
        // * index is within bounds => the pointer stays within bounds
        // * `add` in alignments of T => properly aligned pointer
        // * underlying array exists => points to initalized T
        unsafe { &mut *self.data.add(index) }
    }
}

impl<'a, T: 'a> std::ops::Deref for Dope<'a, T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // SAFETY:
        // * `data` is aligned => pointer is aligned
        // * `data` is initalized => every element is initalized
        // * `data` is one object => slice is over one allocated object
        unsafe { std::slice::from_raw_parts(self.data, self.len) }
    }
}

impl<'a, T: 'a> std::ops::DerefMut for Dope<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY:
        // * `data` is aligned => pointer is aligned
        // * `data` is initalized => every element is initalized
        // * `data` is one object => slice is over one allocated object
        unsafe { std::slice::from_raw_parts_mut(self.data, self.len) }
    }
}

impl<'a, T: 'a> Array<'a> for Dope<'a, T> {}

impl<'a, T: 'a + PartialEq> PartialEq for Dope<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<'a, T: 'a + Eq> std::cmp::Eq for Dope<'a, T> {}
