//! Implementation of [`IterMut`].

use core::ptr::NonNull;

/// Mutable reference [`Iterator`] over an [`Array`](`super::super::Array`).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(in super::super) struct IterMut<'a, T> {
    /// Pointer to the hypothetical next element.
    ptr: NonNull<T>,

    /// Number of elements yet to be yielded.
    count: usize,

    /// Constrain to lifetime of the underlying object.
    lifetime: core::marker::PhantomData<&'a T>,
}

impl<'a, T: 'a> IterMut<'a, T> {
    /// Construct from a pointer to an array and the number of elements.
    ///
    /// # Safety
    /// * `ptr` must have an address aligned for access to `T`.
    /// * `ptr` must point to one contigious allocated object.
    /// * `ptr` must point to `count` consecutive initialized instances of `T`.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    #[must_use]
    pub(in super::super) unsafe fn new(ptr: NonNull<T>, count: usize) -> Self {
        Self {
            ptr,
            count,
            lifetime: core::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    /// Obtain the next element from the front.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    fn next(&mut self) -> Option<Self::Item> {
        (self.count > 0).then(|| {
            // SAFETY:
            // * points to initialized element.
            // * lifetime bound to underlying input.
            let result = unsafe { self.ptr.as_mut() };

            self.ptr = {
                // SAFETY: either within the allocated object or one byte past.
                let ptr = unsafe { self.ptr.as_ptr().add(1) };

                // SAFETY: `add` maintains the non-null requirement.
                unsafe { NonNull::new_unchecked(ptr) }
            };

            self.count = self.count.saturating_sub(1);

            result
        })
    }

    /// Query how many elements have yet to be yielded.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.count, Some(self.count))
    }
}

impl<'a, T: 'a> core::iter::FusedIterator for IterMut<'a, T> {}

impl<'a, T: 'a> ExactSizeIterator for IterMut<'a, T> {}

impl<'a, T: 'a> DoubleEndedIterator for IterMut<'a, T> {
    /// Obtain the next element from the back.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    fn next_back(&mut self) -> Option<Self::Item> {
        (self.count > 0).then(|| {
            self.count = self.count.saturating_sub(1);

            let ptr = self.ptr.as_ptr();

            // SAFETY: points to final element within the allocated object.
            let ptr = unsafe { ptr.add(self.count) };

            // SAFETY:
            // * points to initialized element.
            // * lifetime bound to underlying input.
            unsafe { &mut *ptr }
        })
    }
}

impl<'a, T: 'a + core::fmt::Debug> core::fmt::Debug for IterMut<'a, T> {
    /// Obtain the next element from the back.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let data = self.ptr.as_ptr();
        let len = self.count;

        // SAFETY: points to `len` aligned and initialized instance of `T`.
        let slice = unsafe { core::slice::from_raw_parts(data, len) };

        f.debug_list().entries(slice).finish()
    }
}

#[cfg(test)]
#[allow(
    clippy::undocumented_unsafe_blocks,
    clippy::unwrap_used,
    clippy::expect_used
)]
mod test {
    use super::*;

    mod method {
        use super::*;

        mod new {
            use super::*;

            #[test]
            fn sets_pointer() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let actual = {
                    let ptr = expected.as_mut_ptr();
                    let ptr = unsafe { NonNull::new_unchecked(ptr) };

                    unsafe { IterMut::new(ptr, expected.len()) }
                };

                assert_eq!(actual.ptr.as_ptr(), expected.as_mut_ptr());
            }

            #[test]
            fn sets_elements_count() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let actual = {
                    let ptr = expected.as_mut_ptr();
                    let ptr = unsafe { NonNull::new_unchecked(ptr) };

                    unsafe { IterMut::new(ptr, expected.len()) }
                };

                assert_eq!(actual.count, expected.len());
            }
        }
    }

    mod iterator {
        use super::*;

        #[test]
        fn element_count() {
            let mut expected = [0, 1, 2, 3, 4, 5];

            let actual = {
                let ptr = expected.as_mut_ptr();
                let ptr = unsafe { NonNull::new_unchecked(ptr) };

                unsafe { IterMut::new(ptr, expected.len()) }
            };

            assert_eq!(actual.count(), expected.len());
        }

        #[test]
        fn in_order() {
            let mut expected = [0, 1, 2, 3, 4, 5];

            let actual = {
                let ptr = expected.as_mut_ptr();
                let ptr = unsafe { NonNull::new_unchecked(ptr) };

                unsafe { IterMut::new(ptr, expected.len()) }
            };

            assert!(actual.eq(expected.iter()));
        }

        mod double_ended {
            use super::*;

            #[test]
            fn element_count() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let actual = {
                    let ptr = expected.as_mut_ptr();
                    let ptr = unsafe { NonNull::new_unchecked(ptr) };

                    unsafe { IterMut::new(ptr, expected.len()) }
                }
                .rev();

                assert_eq!(actual.count(), expected.len());
            }

            #[test]
            fn in_order() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let actual = {
                    let ptr = expected.as_mut_ptr();
                    let ptr = unsafe { NonNull::new_unchecked(ptr) };

                    unsafe { IterMut::new(ptr, expected.len()) }
                }
                .rev();

                assert!(actual.eq(expected.iter().rev()));
            }
        }

        mod exact_size {
            use super::*;

            #[test]
            fn hint() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let actual = {
                    let ptr = expected.as_mut_ptr();
                    let ptr = unsafe { NonNull::new_unchecked(ptr) };

                    unsafe { IterMut::new(ptr, expected.len()) }
                };

                assert_eq!(actual.size_hint(), (expected.len(), Some(expected.len())));
            }

            #[test]
            fn len() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let actual = {
                    let ptr = expected.as_mut_ptr();
                    let ptr = unsafe { NonNull::new_unchecked(ptr) };

                    unsafe { IterMut::new(ptr, expected.len()) }
                };

                assert_eq!(actual.len(), expected.len());
            }
            #[test]
            fn updates() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let mut actual = {
                    let ptr = expected.as_mut_ptr();
                    let ptr = unsafe { NonNull::new_unchecked(ptr) };

                    unsafe { IterMut::new(ptr, expected.len()) }
                };

                (0..expected.len()).rev().for_each(|len| {
                    _ = actual.next();

                    assert_eq!(actual.size_hint(), (len, Some(len)));
                });
            }
        }

        mod fused {
            use super::*;

            #[test]
            fn empty() {
                let mut expected: [(); 0] = [];

                let mut actual = {
                    let ptr = expected.as_mut_ptr();
                    let ptr = unsafe { NonNull::new_unchecked(ptr) };

                    unsafe { IterMut::new(ptr, expected.len()) }
                };

                // Yields `None` at least once.
                assert_eq!(actual.next(), None);
                assert_eq!(actual.next_back(), None);

                // Continues to yield `None`.
                assert_eq!(actual.next(), None);
                assert_eq!(actual.next_back(), None);
            }

            #[test]
            fn exhausted() {
                let mut expected = [0];

                let mut actual = {
                    let ptr = expected.as_mut_ptr();
                    let ptr = unsafe { NonNull::new_unchecked(ptr) };

                    unsafe { IterMut::new(ptr, expected.len()) }
                };

                // Exhaust the elements.
                _ = actual.next().expect("the one element");

                // Yields `None` at least once.
                assert_eq!(actual.next(), None);
                assert_eq!(actual.next_back(), None);

                // Continues to yield `None`.
                assert_eq!(actual.next(), None);
                assert_eq!(actual.next_back(), None);
            }
        }
    }
}
