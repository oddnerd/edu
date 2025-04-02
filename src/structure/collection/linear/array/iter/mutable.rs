//! Implementation of [`IterMut`].

use core::ptr::NonNull;

/// Mutable reference [`Iterator`] over an [`Array`](`super::super::Array`).
pub(in super::super) struct IterMut<'a, T> {
    /// Pointer to the hypothetical next element.
    ptr: NonNull<T>,

    /// Number of elements yet to be yielded.
    count: usize,

    /// Constrain to lifetime of the underlying object.
    lifetime: core::marker::PhantomData<&'a mut T>,
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

impl<'a, T: 'a> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    /// Obtain the element with the lowest index yet to be yielded, if any.
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
    fn next(&mut self) -> Option<Self::Item> {
        (self.count > 0).then(|| {
            // SAFETY:
            // * Points to initialized element.
            // * Lifetime bound to underlying input.
            let result = unsafe { self.ptr.as_mut() };

            // SAFETY:
            // * The offset in bytes does not exceed `isize::MAX`.
            // * Stays within the allocated object, or one byte past.
            self.ptr = unsafe { self.ptr.add(1) };

            let Some(decremented) = self.count.checked_sub(1) else {
                unreachable!("executed only if `self.count > 0`");
            };

            self.count = decremented;

            result
        })
    }

    /// Query how many elements have yet to be yielded.
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
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.count, Some(self.count))
    }
}

impl<'a, T: 'a> DoubleEndedIterator for IterMut<'a, T> {
    /// Obtain the element with the greatest index yet to be yielded, if any.
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
    fn next_back(&mut self) -> Option<Self::Item> {
        (self.count > 0).then(|| {
            let Some(decremented) = self.count.checked_sub(1) else {
                unreachable!("executed only if `self.count > 0`");
            };

            self.count = decremented;

            // SAFETY:
            // * The offset in bytes does not exceed `isize::MAX`.
            // * Stays within the allocated object, or one byte past.
            let mut ptr = unsafe { self.ptr.add(self.count) };

            // SAFETY:
            // * Points to initialized element.
            // * Lifetime bound to underlying input.
            unsafe { ptr.as_mut() }
        })
    }
}

impl<'a, T: 'a> ExactSizeIterator for IterMut<'a, T> {}

impl<'a, T: 'a> core::iter::FusedIterator for IterMut<'a, T> {}

impl<'a, T: 'a + core::fmt::Debug> core::fmt::Debug for IterMut<'a, T> {
    /// List the elements yet to be yielded.
    ///
    /// # Performance
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(N) | 𝛀(N) | 𝚯(N) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(N) | 𝛀(N) | 𝚯(N) |
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
            fn when_pointer_is_dangling_and_count_is_zero_then_sets_members() {
                let ptr = NonNull::<usize>::dangling();
                let count = 0;

                let actual = unsafe { IterMut::new(ptr, count) };

                assert_eq!(actual.ptr, ptr);
                assert_eq!(actual.count, 0);
            }

            #[test]
            fn when_pointer_is_not_dangling_and_count_is_non_zero_then_sets_members() {
                let mut underlying = [0, 1, 2, 3, 4, 5];

                let actual = {
                    let ptr = underlying.as_mut_ptr();
                    let ptr = unsafe { NonNull::new_unchecked(ptr) };

                    unsafe { IterMut::new(ptr, underlying.len()) }
                };

                assert_eq!(actual.ptr.as_ptr(), underlying.as_mut_ptr());
                assert_eq!(actual.count, underlying.len());
            }
        }
    }

    mod iterator {
        use super::*;

        mod next {
            use super::*;

            mod when_count_is_zero {
                use super::*;

                #[test]
                fn when_pointer_is_dangling_then_yields_none() {
                    let ptr = NonNull::<usize>::dangling();
                    let count = 0;

                    let mut actual = unsafe { IterMut::new(ptr, count) };

                    assert_eq!(actual.next(), None);
                }

                #[test]
                fn when_pointer_is_not_dangling_then_yields_none() {
                    let mut underlying: [usize; 0] = [];

                    debug_assert!(underlying.is_empty());

                    let ptr = unsafe { NonNull::new_unchecked(underlying.as_mut_ptr()) };
                    let count = underlying.len();

                    let mut actual = unsafe { IterMut::new(ptr, count) };

                    assert_eq!(actual.next(), None);
                }
            }

            mod when_count_is_greater_than_zero {
                use super::*;

                #[test]
                fn then_can_be_advanced_count_times() {
                    let mut underlying = [0, 1, 2, 3, 4, 5];

                    debug_assert!(!underlying.is_empty());

                    let ptr = unsafe { NonNull::new_unchecked(underlying.as_mut_ptr()) };
                    let count = underlying.len();

                    let actual = unsafe { IterMut::new(ptr, count) };

                    assert_eq!(actual.count(), underlying.len());
                }

                #[test]
                fn then_yields_correct_elements_in_correct_order() {
                    let mut underlying = [0, 1, 2, 3, 4, 5];
                    let mut expected = underlying;

                    debug_assert!(!underlying.is_empty());

                    let ptr = unsafe { NonNull::new_unchecked(underlying.as_mut_ptr()) };
                    let count = underlying.len();

                    let actual = unsafe { IterMut::new(ptr, count) };

                    assert!(actual.eq(expected.iter_mut()));
                }

                #[test]
                fn when_yielded_reference_is_mutated_then_underlying_element_is_mutated() {
                    const ELEMENTS: usize = 256;

                    let mut underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                    let mut expected = underlying;
                    expected.reverse();

                    let ptr = unsafe { NonNull::new_unchecked(underlying.as_mut_ptr()) };
                    let count = underlying.len();

                    let mut actual = unsafe { IterMut::new(ptr, count) };

                    for value in (0..ELEMENTS).rev() {
                        let element = actual.next().expect("an element");

                        *element = value;
                    }

                    assert_eq!(underlying, expected);
                }
            }
        }

        mod size_hint {
            use super::*;

            mod when_constructed {
                use super::*;

                #[test]
                fn then_lower_bound_is_count() {
                    for count in 0..256 {
                        let mut underlying: Vec<_> = (0..count).collect();

                        debug_assert_eq!(underlying.len(), count);

                        let ptr = unsafe { NonNull::new_unchecked(underlying.as_mut_ptr()) };

                        let actual = unsafe { IterMut::new(ptr, count) };

                        let (lower, _upper) = actual.size_hint();

                        assert_eq!(lower, count);
                    }
                }

                #[test]
                fn then_upper_bound_is_count() {
                    for count in 0..256 {
                        let mut underlying: Vec<_> = (0..count).collect();

                        debug_assert_eq!(underlying.len(), count);

                        let ptr = unsafe { NonNull::new_unchecked(underlying.as_mut_ptr()) };

                        let actual = unsafe { IterMut::new(ptr, count) };

                        let (_lower, upper) = actual.size_hint();

                        assert_eq!(upper, Some(count));
                    }
                }
            }

            mod when_advanced {
                use super::*;

                #[test]
                fn then_lower_bound_decreases() {
                    let mut underlying: Vec<_> = (0..256).collect();

                    let ptr = unsafe { NonNull::new_unchecked(underlying.as_mut_ptr()) };
                    let count = underlying.len();

                    let mut actual = unsafe { IterMut::new(ptr, count) };

                    for expected in (0..underlying.len()).rev() {
                        _ = actual.next().expect("an element");

                        let (lower, _upper) = actual.size_hint();

                        assert_eq!(lower, expected);
                    }
                }

                #[test]
                fn then_upper_bound_decreases() {
                    let mut underlying: Vec<_> = (0..256).collect();

                    let ptr = unsafe { NonNull::new_unchecked(underlying.as_mut_ptr()) };
                    let count = underlying.len();

                    let mut actual = unsafe { IterMut::new(ptr, count) };

                    for expected in (0..underlying.len()).rev() {
                        _ = actual.next().expect("an element");

                        let (_lower, upper) = actual.size_hint();

                        assert_eq!(upper, Some(expected));
                    }
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

                    unsafe { IterMut::new(ptr, expected.len()) }
                }
                .rev();

                assert_eq!(actual.next(), None);
            }

            #[test]
            fn can_be_advanced_the_number_of_elements_when_underlying_is_not_empty() {
                let expected = [0, 1, 2, 3, 4, 5];
                debug_assert!(!expected.is_empty());

                let mut actual = expected;

                let actual = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { IterMut::new(ptr, actual.len()) }
                }
                .rev();

                assert_eq!(actual.count(), expected.len());
            }

            #[test]
            fn yields_correct_elements_in_correct_order_when_underlying_is_not_empty() {
                let expected = [0, 1, 2, 3, 4, 5];
                debug_assert!(!expected.is_empty());

                let mut actual = expected;

                let actual = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { IterMut::new(ptr, actual.len()) }
                }
                .rev();

                assert!(actual.eq(expected.iter().rev()));
            }

            #[test]
            fn prevents_elements_from_being_yielded_more_than_once_when_advanced_from_both_ends() {
                let underlying = [0, 1];
                debug_assert!(!underlying.is_empty());

                let mut actual = underlying;

                let mut actual = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { IterMut::new(ptr, actual.len()) }
                };

                _ = actual.next().expect("consumes element with value 0");
                _ = actual.next_back().expect("consumes element with value 1");

                assert_eq!(actual.next(), None);
                assert_eq!(actual.next_back(), None);
            }

            #[test]
            fn underlying_element_is_updated_when_yielded_reference_is_mutated() {
                const ELEMENTS: usize = 8;

                let mut actual = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                let mut expected = actual;
                expected.reverse();

                let mut iter = {
                    let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                    unsafe { IterMut::new(ptr, actual.len()) }
                }
                .rev();

                for value in 0..ELEMENTS {
                    let element = iter.next().expect("an element");

                    *element = value;
                }

                assert_eq!(actual, expected);
            }
        }

        mod size_hint {
            use super::*;

            #[test]
            fn lower_bound_updates_when_advanced() {
                const ELEMENTS: usize = 8;

                let mut underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                let mut actual = {
                    let ptr = unsafe { NonNull::new_unchecked(underlying.as_mut_ptr()) };

                    unsafe { IterMut::new(ptr, underlying.len()) }
                }
                .rev();

                for expected in (0..ELEMENTS).rev() {
                    _ = actual.next().expect("an element");

                    let (lower, _upper) = actual.size_hint();

                    assert_eq!(lower, expected);
                }
            }

            #[test]
            fn upper_bound_updates_when_advanced() {
                const ELEMENTS: usize = 8;

                let mut underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                let mut actual = {
                    let ptr = unsafe { NonNull::new_unchecked(underlying.as_mut_ptr()) };

                    unsafe { IterMut::new(ptr, underlying.len()) }
                }
                .rev();

                for expected in (0..ELEMENTS).rev() {
                    _ = actual.next().expect("an element");

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
            let mut underlying: [usize; 0] = [];
            debug_assert!(underlying.is_empty());

            let mut actual = {
                let ptr = unsafe { NonNull::new_unchecked(underlying.as_mut_ptr()) };

                unsafe { IterMut::new(ptr, underlying.len()) }
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
            let mut underlying = [0];

            let mut actual = {
                let ptr = underlying.as_mut_ptr();
                let ptr = unsafe { NonNull::new_unchecked(ptr) };

                unsafe { IterMut::new(ptr, underlying.len()) }
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
        fn is_an_empty_list_when_underlying_is_empty() {
            let expected: [usize; 0] = [];
            debug_assert!(expected.is_empty());

            let mut actual = expected;

            let actual = {
                let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                unsafe { IterMut::new(ptr, actual.len()) }
            };

            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        }

        #[test]
        fn is_a_list_of_the_correct_elements_in_the_correct_order_when_underlying_is_not_empty() {
            let expected = [0, 1, 2, 3, 4, 5];
            debug_assert!(!expected.is_empty());

            let mut actual = expected;

            let actual = {
                let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                unsafe { IterMut::new(ptr, actual.len()) }
            };

            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        }

        #[test]
        fn does_not_contain_elements_yielded_from_the_front() {
            let expected = [0, 1, 2, 3, 4, 5];
            debug_assert!(!expected.is_empty());

            let mut actual = expected;

            let mut actual = {
                let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                unsafe { IterMut::new(ptr, actual.len()) }
            };

            for start in 1..=expected.len() {
                _ = actual.next().expect("an element");

                let expected = &expected[start..];

                assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
            }
        }

        #[test]
        fn does_not_contain_elements_yielded_from_the_back() {
            let expected = [0, 1, 2, 3, 4, 5];
            debug_assert!(!expected.is_empty());

            let mut actual = expected;

            let mut actual = {
                let ptr = unsafe { NonNull::new_unchecked(actual.as_mut_ptr()) };

                unsafe { IterMut::new(ptr, actual.len()) }
            };

            for end in (1..expected.len()).rev() {
                _ = actual.next_back().expect("an element");

                let expected = &expected[..end];

                assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
            }
        }
    }
}
