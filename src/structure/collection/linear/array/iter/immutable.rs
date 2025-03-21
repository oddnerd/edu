//! Implementation of [`Iter`].

use core::ptr::NonNull;

/// Immutable reference [`Iterator`] over an [`Array`](`super::super::Array`).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(in super::super) struct Iter<'a, T> {
    /// Pointer to the hypothetical next element.
    ptr: NonNull<T>,

    /// Number of elements yet to be yielded.
    count: usize,

    /// Constrain to lifetime of the underlying object.
    lifetime: core::marker::PhantomData<&'a T>,
}

impl<'a, T: 'a> Iter<'a, T> {
    /// Construct from a pointer to an array and the number of elements.
    ///
    /// # Safety
    /// * `ptr` must have an address aligned for access to `T`.
    /// * `ptr` must point to one contigious allocated object.
    /// * `ptr` must point to `count` consecutive initialized instances of `T`.
    ///
    /// # Performance
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    #[must_use]
    pub(in super::super) unsafe fn new(ptr: NonNull<T>, count: usize) -> Self {
        Self {
            ptr,
            count,
            lifetime: core::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = &'a T;

    /// Obtain the next element from the front.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    fn next(&mut self) -> Option<Self::Item> {
        (self.count > 0).then(|| {
            // SAFETY:
            // * points to initialized element.
            // * lifetime bound to underlying input.
            let result = unsafe { self.ptr.as_ref() };

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

impl<'a, T: 'a> core::iter::FusedIterator for Iter<'a, T> {}

impl<'a, T: 'a> ExactSizeIterator for Iter<'a, T> {}

impl<'a, T: 'a> DoubleEndedIterator for Iter<'a, T> {
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
            unsafe { &*ptr }
        })
    }
}

impl<'a, T: 'a + core::fmt::Debug> core::fmt::Debug for Iter<'a, T> {
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

                    unsafe { Iter::new(ptr, expected.len()) }
                };

                assert_eq!(actual.ptr.as_ptr(), expected.as_mut_ptr());
            }

            #[test]
            fn sets_elements_count() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let actual = {
                    let ptr = expected.as_mut_ptr();
                    let ptr = unsafe { NonNull::new_unchecked(ptr) };

                    unsafe { Iter::new(ptr, expected.len()) }
                };

                assert_eq!(actual.count, expected.len());
            }
        }
    }

    mod iterator {
        use super::*;

        mod next {
            use super::*;

            #[test]
            fn yields_none_when_underlying_is_empty() {
                let mut expected: [usize; 0] = [];
                debug_assert!(expected.is_empty());

                let mut actual = {
                    let ptr = unsafe { NonNull::new_unchecked(expected.as_mut_ptr()) };

                    unsafe { Iter::new(ptr, expected.len()) }
                };

                assert_eq!(actual.next(), None);
            }

            #[test]
            fn can_be_advanced_the_number_of_elements_when_underlying_is_not_empty() {
                let expected = [0, 1, 2, 3, 4, 5];
                debug_assert!(!expected.is_empty());

                let mut actual = expected;

                let actual = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { Iter::new(ptr, actual.len()) }
                };

                assert_eq!(actual.count(), expected.len());
            }

            #[test]
            fn yields_correct_elements_in_correct_order_when_underlying_is_not_empty() {
                let expected = [0, 1, 2, 3, 4, 5];
                debug_assert!(!expected.is_empty());

                let mut actual = expected;

                let actual = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { Iter::new(ptr, actual.len()) }
                };

                assert!(actual.eq(expected.iter()));
            }
        }

        mod size_hint {
            use super::*;

            #[test]
            fn lower_bound_is_number_of_elements_when_constructed() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual = expected;

                let actual = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { Iter::new(ptr, actual.len()) }
                };

                let (lower, _upper) = actual.size_hint();

                assert_eq!(lower, expected.len());
            }

            #[test]
            fn lower_bound_updates_when_advanced() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual = expected;

                let mut actual = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { Iter::new(ptr, actual.len()) }
                };

                #[expect(clippy::shadow_unrelated, reason = "derived from length")]
                for expected in (0..expected.len()).rev() {
                    _ = actual.next();

                    let (lower, _upper) = actual.size_hint();

                    assert_eq!(lower, expected);
                }
            }

            #[test]
            fn upper_bound_is_number_of_elements_when_constructed() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual = expected;

                let actual = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { Iter::new(ptr, actual.len()) }
                };

                let (_lower, upper) = actual.size_hint();

                assert_eq!(upper, Some(expected.len()));
            }

            #[test]
            fn upper_bound_updates_when_advanced() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual = expected;

                let mut actual = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { Iter::new(ptr, actual.len()) }
                };

                #[expect(clippy::shadow_unrelated, reason = "derived from length")]
                for expected in (0..expected.len()).rev() {
                    _ = actual.next();

                    let (_lower, upper) = actual.size_hint();

                    assert_eq!(upper, Some(expected));
                }
            }
        }
    }

    mod double_ended_iterator {
        use super::*;

        mod next_back {
            use super::*;

            #[test]
            fn yields_none_when_underlying_is_empty() {
                let mut expected: [usize; 0] = [];
                debug_assert!(expected.is_empty());

                let mut actual = {
                    let ptr = unsafe { NonNull::new_unchecked(expected.as_mut_ptr()) };

                    unsafe { Iter::new(ptr, expected.len()) }
                }.rev();

                assert_eq!(actual.next(), None);
            }

            #[test]
            fn can_be_advanced_the_number_of_elements_when_underlying_is_not_empty() {
                let expected = [0, 1, 2, 3, 4, 5];
                debug_assert!(!expected.is_empty());

                let mut actual = expected;

                let actual = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { Iter::new(ptr, actual.len()) }
                }.rev();

                assert_eq!(actual.count(), expected.len());
            }

            #[test]
            fn yields_correct_elements_in_correct_order_when_underlying_is_not_empty() {
                let expected = [0, 1, 2, 3, 4, 5];
                debug_assert!(!expected.is_empty());

                let mut actual = expected;

                let actual = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { Iter::new(ptr, actual.len()) }
                }.rev();

                assert!(actual.eq(expected.iter()));
            }

            #[test]
            fn prevents_elements_from_being_yielded_more_than_once_when_advanced_from_both_ends() {
                let expected = [0, 1];
                debug_assert!(!expected.is_empty());

                let mut actual = expected;

                let mut actual = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { Iter::new(ptr, actual.len()) }
                };

                _ = actual.next();      // Consumes element '0'.
                _ = actual.next_back(); // Consumes element '1'.

                assert_eq!(actual.next(), None);
                assert_eq!(actual.next_back(), None);
            }
        }

        mod size_hint {
            use super::*;

            #[test]
            fn lower_bound_updates_when_advanced() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual = expected;

                let mut actual = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { Iter::new(ptr, actual.len()) }
                }.rev();

                #[expect(clippy::shadow_unrelated, reason = "derived from length")]
                for expected in (0..expected.len()).rev() {
                    _ = actual.next();

                    let (lower, _upper) = actual.size_hint();

                    assert_eq!(lower, expected);
                }
            }

            #[test]
            fn upper_bound_updates_when_advanced() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual = expected;

                let mut actual = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { Iter::new(ptr, actual.len()) }
                }.rev();

                #[expect(clippy::shadow_unrelated, reason = "derived from length")]
                for expected in (0..expected.len()).rev() {
                    _ = actual.next();

                    let (_lower, upper) = actual.size_hint();

                    assert_eq!(upper, Some(expected));
                }
            }
        }
    }

    mod fused_iterator {
        use super::*;

        #[test]
        fn continues_to_yield_none_when_underlying_is_empty() {
            let mut expected: [usize; 0] = [];

            let mut actual = {
                let ptr = unsafe { NonNull::new_unchecked(expected.as_mut_ptr()) };

                unsafe { Iter::new(ptr, expected.len()) }
            };

            // Yields `None` at least once.
            assert_eq!(actual.next(), None);
            assert_eq!(actual.next_back(), None);

            // Continues to yield `None`.
            assert_eq!(actual.next(), None);
            assert_eq!(actual.next_back(), None);
        }

        #[test]
        fn continues_to_yield_none_when_underlying_is_exhausted() {
            let mut expected = [0];

            let mut actual = {
                let ptr = expected.as_mut_ptr();
                let ptr = unsafe { NonNull::new_unchecked(ptr) };

                unsafe { Iter::new(ptr, expected.len()) }
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

    mod debug {
        use super::*;

        #[test]
        fn is_elements() {
            let mut expected = [0, 1, 2, 3, 4, 5];

            let actual = {
                let ptr = expected.as_mut_ptr();
                let ptr = unsafe { NonNull::new_unchecked(ptr) };

                unsafe { Iter::new(ptr, expected.len()) }
            };

            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        }
    }
}
