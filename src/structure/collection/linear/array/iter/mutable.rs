//! Implementation of [`IterMut`].

/// Mutable reference [`Iterator`] over an [`super::super::Array`].
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct IterMut<'a, T> {
    /// Pointer to the hypothetical next element.
    ptr: std::ptr::NonNull<T>,

    /// Number of elements yet to be yielded.
    count: usize,

    /// Constrain to lifetime of the underlying object.
    lifetime: std::marker::PhantomData<&'a T>,
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
    pub unsafe fn new(ptr: std::ptr::NonNull<T>, count: usize) -> Self {
        Self {
            ptr,
            count,
            lifetime: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    /// Obtain the next element from the front.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::iter::IterMut;
    ///
    /// let mut underlying = [0, 1, 2, 3, 4, 5];
    /// let ptr = std::ptr::NonNull::new(underlying.as_mut_ptr()).unwrap();
    /// let mut iter = unsafe { IterMut::new(ptr, underlying.len()) };
    ///
    /// assert_eq!(iter.next(), Some(&mut 0));
    /// assert_eq!(iter.next(), Some(&mut 1));
    /// assert_eq!(iter.next(), Some(&mut 2));
    /// assert_eq!(iter.next(), Some(&mut 3));
    /// assert_eq!(iter.next(), Some(&mut 4));
    /// assert_eq!(iter.next(), Some(&mut 5));
    /// assert_eq!(iter.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        if self.count > 0 {
            // SAFETY:
            // * points to initialized element.
            // * lifetime bound to underlying input.
            let result = unsafe { self.ptr.as_mut() };

            self.ptr = unsafe {
                // SAFETY: either within the allocated object or one byte past.
                let ptr = self.ptr.as_ptr().add(1);

                // SAFETY: `add` maintains the non-null requirement.
                std::ptr::NonNull::new_unchecked(ptr)
            };
            self.count -= 1;

            Some(result)
        } else {
            None
        }
    }

    /// Query how many elements have yet to be yielded.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::iter::IterMut;
    ///
    /// let mut underlying = [0, 1, 2, 3, 4, 5];
    /// let ptr = std::ptr::NonNull::new(underlying.as_mut_ptr()).unwrap();
    /// let iter = unsafe { IterMut::new(ptr, underlying.len()) };
    ///
    /// assert_eq!(iter.size_hint(), (6, Some(6)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.count, Some(self.count))
    }
}

impl<'a, T: 'a> std::iter::FusedIterator for IterMut<'a, T> {}

impl<'a, T: 'a> ExactSizeIterator for IterMut<'a, T> {}

impl<'a, T: 'a> DoubleEndedIterator for IterMut<'a, T> {
    /// Obtain the next element from the back.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::iter::IterMut;
    ///
    /// let mut underlying = [0, 1, 2, 3, 4, 5];
    /// let ptr = std::ptr::NonNull::new(underlying.as_mut_ptr()).unwrap();
    /// let mut iter = unsafe { IterMut::new(ptr, underlying.len()) };
    ///
    /// assert_eq!(iter.next_back(), Some(&mut 5));
    /// assert_eq!(iter.next_back(), Some(&mut 4));
    /// assert_eq!(iter.next_back(), Some(&mut 3));
    /// assert_eq!(iter.next_back(), Some(&mut 2));
    /// assert_eq!(iter.next_back(), Some(&mut 1));
    /// assert_eq!(iter.next_back(), Some(&mut 0));
    /// assert_eq!(iter.next_back(), None);
    /// ```
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.count > 0 {
            self.count -= 1;

            Some(unsafe {
                // SAFETY: points to final element within the allocated object.
                let ptr = self.ptr.as_ptr().add(self.count);

                // SAFETY:
                // * points to initialized element.
                // * lifetime bound to underlying input.
                ptr.as_mut().unwrap_unchecked()
            })
        } else {
            None
        }
    }
}

impl<'a, T: 'a + std::fmt::Debug> std::fmt::Debug for IterMut<'a, T> {
    /// Obtain the next element from the back.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::iter::IterMut;
    ///
    /// let mut underlying = [0, 1, 2, 3, 4, 5];
    /// let ptr = std::ptr::NonNull::new(underlying.as_mut_ptr()).unwrap();
    /// let mut iter = unsafe { IterMut::new(ptr, underlying.len()) };
    ///
    /// // Remove some elements.
    /// iter.next();
    /// iter.next_back();
    ///
    /// assert_eq!(format!("{iter:?}"), format!("[1, 2, 3, 4]"));
    ///
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // SAFETY: points to `count` initialized instance of `T`.
        let slice = unsafe { std::slice::from_raw_parts(self.ptr.as_ptr(), self.count) };
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

                let actual = unsafe {
                    let ptr = expected.as_mut_ptr();
                    let ptr = std::ptr::NonNull::new(ptr).unwrap();

                    IterMut::new(ptr, expected.len())
                };

                assert_eq!(actual.ptr.as_ptr(), expected.as_mut_ptr());
            }

            #[test]
            fn sets_elements_count() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let actual = unsafe {
                    let ptr = expected.as_mut_ptr();
                    let ptr = std::ptr::NonNull::new(ptr).unwrap();

                    IterMut::new(ptr, expected.len())
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

            let actual = unsafe {
                let ptr = expected.as_mut_ptr();
                let ptr = std::ptr::NonNull::new(ptr).unwrap();

                IterMut::new(ptr, expected.len())
            };

            assert_eq!(actual.count(), expected.len());
        }

        #[test]
        fn in_order() {
            let mut expected = [0, 1, 2, 3, 4, 5];

            let actual = unsafe {
                let ptr = expected.as_mut_ptr();
                let ptr = std::ptr::NonNull::new(ptr).unwrap();

                IterMut::new(ptr, expected.len())
            };

            assert!(actual.eq(expected.iter()));
        }

        mod double_ended {
            use super::*;

            #[test]
            fn element_count() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let actual = unsafe {
                    let ptr = expected.as_mut_ptr();
                    let ptr = std::ptr::NonNull::new(ptr).unwrap();

                    IterMut::new(ptr, expected.len())
                };

                assert_eq!(actual.rev().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let actual = unsafe {
                    let ptr = expected.as_mut_ptr();
                    let ptr = std::ptr::NonNull::new(ptr).unwrap();

                    IterMut::new(ptr, expected.len())
                };

                assert!(actual.rev().eq(expected.iter().rev()));
            }
        }

        mod exact_size {
            use super::*;

            #[test]
            fn hint() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let actual = unsafe {
                    let ptr = expected.as_mut_ptr();
                    let ptr = std::ptr::NonNull::new(ptr).unwrap();

                    IterMut::new(ptr, expected.len())
                };

                assert_eq!(actual.size_hint(), (expected.len(), Some(expected.len())));
            }

            #[test]
            fn len() {
                let mut expected = [0, 1, 2, 3, 4, 5];

                let actual = unsafe {
                    let ptr = expected.as_mut_ptr();
                    let ptr = std::ptr::NonNull::new(ptr).unwrap();

                    IterMut::new(ptr, expected.len())
                };

                assert_eq!(actual.len(), expected.len());
            }
        }

        mod fused {
            use super::*;

            #[test]
            fn empty() {
                let mut expected: [(); 0] = [];

                let mut actual = unsafe {
                    let ptr = expected.as_mut_ptr();
                    let ptr = std::ptr::NonNull::new(ptr).unwrap();

                    IterMut::new(ptr, expected.len())
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

                let mut actual = unsafe {
                    let ptr = expected.as_mut_ptr();
                    let ptr = std::ptr::NonNull::new(ptr).unwrap();

                    IterMut::new(ptr, expected.len())
                };

                // Exhaust the elements.
                let _ = actual.next().expect("the one element");

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
