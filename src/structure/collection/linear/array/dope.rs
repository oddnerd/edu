//! Implementation of [`Dope`].

use super::Array;
use super::Collection;
use super::Linear;

use core::ptr::NonNull;

/// Lightweight access to a contigious buffer of memory.
///
/// A [Dope Vector](https://en.wikipedia.org/wiki/Dope_vector) comprises of a
/// pointer and length pair leveraging compile-time type information alongside
/// pointer arithmetic to distinguish between individual elements.
///
/// This is equivalent to Rust's slice ([`[T]`]([`slice`])) or C++'s span
/// ([`std::span`][span]) and views ([`std::string_view`][string_view]).
///
/// Note that is is strictly a mutable variant, hence you cannot safely
/// construct an instance from memory you only have an immutable reference to,
/// even if you promise to not call mutable methods. The expected use case is
/// constructing from _owned_ memory.
///
/// [span]: https://en.cppreference.com/w/cpp/container/span
/// [string_view]: https://en.cppreference.com/w/cpp/string/basic_string_view
pub struct Dope<'a, T> {
    /// Pointer to the start of the array.
    ptr: NonNull<T>,

    /// Number of elements within the array.
    count: usize,

    /// Bind lifetime to underlying memory buffer.
    lifetime: core::marker::PhantomData<&'a mut T>,
}

impl<'a, T: 'a> Dope<'a, T> {
    /// Construct from a pointer to an array and the number of elements.
    ///
    /// # Safety
    /// * `ptr` must have an address aligned for access to `T`.
    /// * `ptr` must point to one contigious allocated object.
    /// * `ptr` must point to `len` consecutive initialized instances of `T`.
    ///
    /// # Performance
    /// This method always consumes O(1) memory and takes O(1) time.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    ///
    /// let Some(ptr) = core::ptr::NonNull::new(expected.as_mut_ptr()) else {
    ///     unreachable!("points to the array");
    /// };
    ///
    /// // SAFETY: points to that many consecutive initialized integers.
    /// let actual = unsafe { Dope::new(ptr, expected.len()) };
    ///
    /// assert!(actual.iter().eq(expected.iter()));
    /// ```
    #[must_use]
    pub unsafe fn new(ptr: NonNull<T>, count: usize) -> Self {
        Self {
            ptr,
            count,
            lifetime: core::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> From<&'a mut [T]> for Dope<'a, T> {
    /// Construct from an existing mutable [`slice`].
    ///
    /// # Performance
    /// This method always consumes O(1) memory and takes O(1) time.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    ///
    /// let mut actual = expected.clone();
    /// let actual = Dope::from(actual.as_mut_slice());
    ///
    /// assert!(actual.iter().eq(expected.iter()));
    /// ```
    #[must_use]
    fn from(slice: &'a mut [T]) -> Self {
        Self {
            ptr: NonNull::new(slice.as_mut_ptr())
                .unwrap_or_else(|| unreachable!("slice will not yield null pointer")),
            count: slice.len(),
            lifetime: core::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a + PartialEq> PartialEq for Dope<'a, T> {
    /// Query if the elements have the same values and order as `other`.
    ///
    /// # Performance
    /// This method always consumes O(1) memory and takes O(N) time.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut left = [0, 1, 2, 3, 4, 5];
    /// let mut right = left.clone();
    ///
    /// // Note that these point to different memory, but same values.
    /// let left = unsafe { Dope::from(left.as_mut_slice()) };
    /// let right = unsafe { Dope::from(right.as_mut_slice()) };
    ///
    /// assert_eq!(left, right);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<'a, T: 'a + Eq> Eq for Dope<'a, T> {}

impl<'a, T: 'a> core::ops::Index<usize> for Dope<'a, T> {
    type Output = T;

    /// Obtain a reference to the element `index` positions from the start.
    ///
    /// # Panics
    /// If provided `index` is out of bounds.
    ///
    /// # Performance
    /// This method always consumes O(1) memory and takes O(1) time.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    ///
    /// let actual = Dope::from(expected.as_mut_slice());
    ///
    /// for index in 0..=5 {
    ///     use core::ops::Index;
    ///
    ///     assert_eq!(actual.index(index), &index);
    /// }
    /// ```
    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < self.count, "index out of bounds");

        // SAFETY:
        // * The offset in bytes does not exceed `isize::MAX`.
        // * Stays within the allocated object, or one byte past.
        let ptr = unsafe { self.ptr.add(index) };

        // SAFETY:
        // * Points to initialized element.
        // * Lifetime bound to underlying input.
        unsafe { ptr.as_ref() }
    }
}

impl<'a, T: 'a> core::ops::IndexMut<usize> for Dope<'a, T> {
    /// Obtain a reference to the element `index` positions from the start.
    ///
    /// # Panics
    /// If provided `index` is out of bounds.
    ///
    /// # Performance
    /// This method always consumes O(1) memory and takes O(1) time.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    ///
    /// let mut actual = Dope::from(expected.as_mut_slice());
    ///
    /// for mut index in 0..=5 {
    ///     use core::ops::IndexMut;
    ///
    ///     assert_eq!(actual.index_mut(index), &mut index);
    /// }
    /// ```
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert!(index < self.count, "index out of bounds");

        // SAFETY:
        // * The offset in bytes does not exceed `isize::MAX`.
        // * Stays within the allocated object, or one byte past.
        let mut ptr = unsafe { self.ptr.add(index) };

        // SAFETY:
        // * Points to initialized element.
        // * Lifetime bound to underlying input.
        unsafe { ptr.as_mut() }
    }
}

impl<'a, T: 'a + core::fmt::Debug> core::fmt::Debug for Dope<'a, T> {
    /// List the elements referenced to/contained.
    ///
    /// # Performance
    /// This method always consumes O(N) memory and takes O(N) time.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    ///
    /// let actual = Dope::from(expected.as_mut_slice());
    ///
    /// assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    /// ```
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<'a, T: 'a> Collection for Dope<'a, T> {
    type Element = T;

    /// Query how many elements are referenced to/contained.
    ///
    /// # Performance
    /// This method always consumes O(1) memory and takes O(1) time.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::Collection;
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    ///
    /// let actual = Dope::from(expected.as_mut_slice());
    ///
    /// assert_eq!(Collection::count(&actual), expected.len());
    /// ```
    fn count(&self) -> usize {
        self.count
    }
}

impl<'a, T: 'a> Linear for Dope<'a, T> {
    /// Immutably iterate the elements in order.
    ///
    /// # Performance
    /// This method always consumes O(1) memory and takes O(1) time.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    ///
    /// let actual = Dope::from(expected.as_mut_slice());
    ///
    /// for (index, element) in actual.iter().enumerate() {
    ///     assert_eq!(element, &index);
    /// }
    /// ```
    fn iter(
        &self,
    ) -> impl DoubleEndedIterator<Item = &Self::Element> + ExactSizeIterator + core::iter::FusedIterator
    {
        // SAFETY:
        // * Pointer is aligned.
        // * Points to one allocated object.
        // * Points to `count` contigious initialized instance of `T`.
        unsafe { super::Iter::new(self.ptr, self.count) }
    }

    /// Mutably iterate the elements in order.
    ///
    /// # Performance
    /// This method always consumes O(1) memory and takes O(1) time.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Linear;
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    ///
    /// let mut actual = Dope::from(expected.as_mut_slice());
    ///
    /// for (mut index, element) in actual.iter_mut().enumerate() {
    ///     assert_eq!(element, &mut index);
    /// }
    /// ```
    fn iter_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = &mut Self::Element>
    + ExactSizeIterator
    + core::iter::FusedIterator {
        // SAFETY:
        // * Pointer is aligned.
        // * Points to one allocated object.
        // * Points to `count` contigious initialized instance of `T`.
        unsafe { super::IterMut::new(self.ptr, self.count) }
    }
}

impl<'a, T: 'a> Array for Dope<'a, T> {
    /// Obtain an immutable pointer to the underlying contigious memory buffer.
    ///
    /// # Safety
    /// `self` must outlive the resultant pointer.
    ///
    /// # Performance
    /// This method always consumes O(1) memory and takes O(1) time.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Array;
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    ///
    /// let actual = Dope::from(expected.as_mut_slice());
    ///
    /// assert_eq!(actual.as_ptr(), expected.as_ptr());
    /// ```
    fn as_ptr(&self) -> *const Self::Element {
        self.ptr.as_ptr().cast_const()
    }

    /// Obtain an immutable pointer to the underlying contigious memory buffer.
    ///
    /// # Safety
    /// `self` must outlive the resultant pointer.
    ///
    /// # Performance
    /// This method always consumes O(1) memory and takes O(1) time.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Array;
    /// use rust::structure::collection::linear::array::Dope;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    ///
    /// let mut actual = Dope::from(expected.as_mut_slice());
    ///
    /// assert_eq!(actual.as_mut_ptr(), expected.as_mut_ptr());
    /// ```
    fn as_mut_ptr(&mut self) -> *mut Self::Element {
        self.ptr.as_ptr()
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
            fn when_underlying_is_empty_then_sets_members() {
                let mut underlying: [usize; 0] = [];

                debug_assert!(underlying.is_empty());

                let ptr = unsafe { NonNull::new_unchecked(underlying.as_mut_ptr()) };
                let count = underlying.len();

                let actual = unsafe { Dope::new(ptr, count) };

                assert_eq!(actual.ptr.as_ptr(), underlying.as_mut_ptr());
                assert_eq!(actual.count, underlying.len());
            }

            #[test]
            fn when_underlying_is_not_empty_then_sets_members() {
                let mut underlying = [0, 1, 2, 3, 4, 5];

                debug_assert!(!underlying.is_empty());

                let ptr = unsafe { NonNull::new_unchecked(underlying.as_mut_ptr()) };
                let count = underlying.len();

                let actual = unsafe { Dope::new(ptr, count) };

                assert_eq!(actual.ptr.as_ptr(), underlying.as_mut_ptr());
                assert_eq!(actual.count, underlying.len());
            }
        }
    }

    mod from {
        use super::*;

        mod slice {
            use super::*;

            #[test]
            fn when_underlying_is_empty_then_sets_members() {
                let mut underlying: [usize; 0] = [];

                let underlying = underlying.as_mut_slice();

                let ptr = underlying.as_mut_ptr();
                let count = underlying.len();

                debug_assert!(underlying.is_empty());

                let actual = Dope::from(underlying);

                assert_eq!(actual.ptr.as_ptr(), ptr);
                assert_eq!(actual.count, count);
            }

            #[test]
            fn when_underlying_is_not_empty_then_sets_members() {
                let mut underlying = [0, 1, 2, 3, 4, 5];

                let underlying = underlying.as_mut_slice();

                let ptr = underlying.as_mut_ptr();
                let count = underlying.len();

                debug_assert!(!underlying.is_empty());

                let actual = Dope::from(underlying);

                assert_eq!(actual.ptr.as_ptr(), ptr);
                assert_eq!(actual.count, count);
            }
        }
    }

    mod partial_equality {
        use super::*;

        #[test]
        fn when_both_empty_then_equivalent() {
            let mut a: [usize; 0] = [];
            let a = Dope::from(a.as_mut_slice());

            let mut b: [usize; 0] = [];
            let b = Dope::from(b.as_mut_slice());

            debug_assert!(a.is_empty());
            debug_assert!(b.is_empty());

            assert_eq!(a, b);
        }

        #[test]
        fn when_different_length_and_same_subset_then_not_equivalent() {
            for length in 2..256 {
                let mut a: Vec<_> = (0..length).collect();

                for subset in 1..length {
                    let mut b = a[..subset].to_vec();

                    debug_assert_eq!(a[..subset], b[..]);

                    let a = Dope::from(a.as_mut_slice());
                    let b = Dope::from(b.as_mut_slice());

                    assert_ne!(a, b);
                }
            }
        }

        #[test]
        fn when_same_length_and_different_element_then_inequivalent() {
            for length in 1..256 {
                let mut a: Vec<_> = (0..length).collect();
                let mut b: Vec<_> = (0..length).collect();

                debug_assert_eq!(a.len(), b.len());

                for different in 0..length {
                    b[different] = 12345;

                    debug_assert_ne!(a[different], b[different]);
                }

                let a = Dope::from(a.as_mut_slice());
                let b = Dope::from(b.as_mut_slice());

                assert_ne!(a, b);
            }
        }

        #[test]
        fn when_same_length_and_same_elements_but_different_order_then_inequivalent() {
            for length in 2..32 {
                let mut a: Vec<_> = (0..length).collect();
                let mut b: Vec<_> = (0..length).collect();

                debug_assert_eq!(a.len(), b.len());
                debug_assert_eq!(a, b);

                for _ in 1..length {
                    b.rotate_right(1);

                    debug_assert_ne!(a, b);

                    let a = Dope::from(a.as_mut_slice());
                    let b = Dope::from(b.as_mut_slice());

                    assert_ne!(a, b);
                }
            }
        }

        #[test]
        fn when_same_length_and_same_element_and_same_order_then_equivalent() {
            for length in 1..256 {
                let mut a: Vec<_> = (0..length).collect();
                let mut b: Vec<_> = (0..length).collect();

                debug_assert_eq!(a, b);

                let a = Dope::from(a.as_mut_slice());
                let b = Dope::from(b.as_mut_slice());

                assert_eq!(a, b);
            }
        }

        #[test]
        fn when_equivalent_then_is_symmetric() {
            // a == b <=> b == a

            for length in 0..256 {
                let mut a: Vec<_> = (0..length).collect();
                let mut b: Vec<_> = (0..length).collect();

                debug_assert_eq!(a, b);

                let a = Dope::from(a.as_mut_slice());
                let b = Dope::from(b.as_mut_slice());

                assert_eq!(a, b);
                assert_eq!(b, a);
            }
        }

        #[test]
        fn when_equivalent_then_is_transitive() {
            // a == b && b == c <=> a == c

            for length in 0..256 {
                let mut a: Vec<_> = (0..length).collect();
                let mut b: Vec<_> = (0..length).collect();
                let mut c: Vec<_> = (0..length).collect();

                debug_assert_eq!(a, b);
                debug_assert_eq!(b, c);
                debug_assert_eq!(a, c);

                let a = Dope::from(a.as_mut_slice());
                let b = Dope::from(b.as_mut_slice());
                let c = Dope::from(c.as_mut_slice());

                assert_eq!(a, b);
                assert_eq!(b, a);
                assert_eq!(a, c);
            }
        }
    }

    mod equality {
        use super::*;

        #[test]
        fn when_compared_against_self_then_is_equivalent() {
            for length in 0..256 {
                let mut underlying: Vec<_> = (0..length).collect();

                let actual = Dope::from(underlying.as_mut_slice());

                assert_eq!(actual, actual);
            }
        }
    }

    mod index {
        use super::*;

        use core::ops::Index as _;

        #[test]
        #[should_panic = "index out of bounds"]
        fn when_empty_then_panics() {
            let mut underlying: [usize; 0] = [];

            let actual = Dope::from(underlying.as_mut_slice());

            _ = actual.index(0);
        }

        #[test]
        #[should_panic = "index out of bounds"]
        fn when_index_is_out_of_bounds_then_panics() {
            let mut underlying = [0, 1, 2, 3, 4, 5];

            let actual = Dope::from(underlying.as_mut_slice());

            _ = actual.index(6);
        }

        #[test]
        fn when_index_is_within_bounds_then_yields_correct_element() {
            // Note that value of each underlying element is not merely its
            // index to ensure the element instead of its index is yielded.

            let mut underlying: Vec<_> = (0..256).rev().collect();

            let actual = Dope::from(underlying.as_mut_slice());

            for (index, expected) in (0..256).rev().enumerate() {
                assert_eq!(actual.index(index), &expected);
            }
        }
    }

    mod index_mut {
        use super::*;

        use core::ops::IndexMut as _;

        #[test]
        #[should_panic = "index out of bounds"]
        fn when_empty_then_panics() {
            let mut underlying: [usize; 0] = [];

            let mut actual = Dope::from(underlying.as_mut_slice());

            _ = actual.index_mut(0);
        }

        #[test]
        #[should_panic = "index out of bounds"]
        fn when_index_is_out_of_bounds_then_panics() {
            let mut underlying = [0, 1, 2, 3, 4, 5];

            let mut actual = Dope::from(underlying.as_mut_slice());

            _ = actual.index_mut(6);
        }

        #[test]
        fn when_index_is_within_bounds_then_yields_correct_element() {
            // Note that value of each underlying element is not merely its
            // index to ensure the element instead of its index is yielded.

            let mut underlying: Vec<_> = (0..256).rev().collect();

            let mut actual = Dope::from(underlying.as_mut_slice());

            for (index, expected) in (0..256).rev().enumerate() {
                assert_eq!(actual.index_mut(index), &expected);
            }
        }

        #[test]
        fn when_yielded_reference_is_mutated_then_underlying_element_is_mutated() {
            for mutated in 0..256 {
                let mut underlying: Vec<_> = (0..256).collect();

                let mut actual = Dope::from(underlying.as_mut_slice());

                *actual.index_mut(mutated) = 12345;

                for (index, element) in underlying.iter().enumerate() {
                    if index == mutated {
                        assert_eq!(element, &12345);
                    } else {
                        assert_eq!(element, &index);
                    }
                }
            }
        }
    }

    mod debug {
        use super::*;

        #[test]
        fn when_empty_then_is_empty_list() {
            let mut underlying: [usize; 0] = [];
            let expected = underlying;

            debug_assert!(underlying.is_empty());

            let actual = Dope::from(underlying.as_mut_slice());

            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        }

        #[test]
        fn when_not_empty_then_is_correct_elements_in_correct_order() {
            for length in 1..256 {
                let mut underlying: Vec<_> = (0..length).collect();
                let expected = underlying.clone();

                debug_assert!(!underlying.is_empty());

                let actual = Dope::from(underlying.as_mut_slice());

                assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
            }
        }
    }

    mod collection {
        use super::*;

        mod count {
            use super::*;

            #[test]
            fn when_empty_then_yields_zero() {
                let mut underlying: [usize; 0] = [];

                debug_assert!(underlying.is_empty());

                let actual = Dope::from(underlying.as_mut_slice());

                assert_eq!(actual.count(), 0);
            }

            #[test]
            fn when_not_empty_then_is_number_of_elements() {
                let mut underlying: Vec<_> = (0..256).collect();

                for length in 1..=underlying.len() {
                    let underlying = &mut underlying[..length];

                    debug_assert_eq!(underlying.len(), length);

                    let actual = Dope::from(underlying);

                    assert_eq!(actual.count(), length);
                }
            }
        }
    }

    mod linear {
        use super::*;

        mod iter {
            use super::*;

            mod iterator {
                use super::*;

                mod next {
                    use super::*;

                    #[test]
                    fn when_empty_then_yields_none() {
                        let mut underlying: [usize; 0] = [];

                        debug_assert!(underlying.is_empty());

                        let actual = Dope::from(underlying.as_mut_slice());

                        let mut actual = actual.iter();

                        assert_eq!(actual.next(), None);
                    }

                    mod when_not_empty {
                        use super::*;

                        #[test]
                        fn then_can_be_advanced_count_times() {
                            for length in 1..256 {
                                let mut underlying: Vec<_> = (0..length).collect();

                                debug_assert!(!underlying.is_empty());
                                debug_assert_eq!(underlying.len(), length);

                                let actual = Dope::from(underlying.as_mut_slice());

                                let actual = actual.iter();

                                assert_eq!(actual.count(), length);
                            }
                        }

                        #[test]
                        fn then_yields_correct_elements_in_correct_order() {
                            for length in 1..256 {
                                let mut underlying: Vec<_> = (0..length).collect();
                                let expected = underlying.clone();

                                debug_assert!(!underlying.is_empty());
                                debug_assert_eq!(underlying.len(), length);

                                let actual = Dope::from(underlying.as_mut_slice());

                                let actual = actual.iter();

                                assert!(actual.eq(expected.iter()));
                            }
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

                                let actual = Dope::from(underlying.as_mut_slice());

                                let actual = actual.iter();

                                let (lower, _upper) = actual.size_hint();

                                assert_eq!(lower, count);
                            }
                        }

                        #[test]
                        fn then_upper_bound_is_count() {
                            for count in 0..256 {
                                let mut underlying: Vec<_> = (0..count).collect();

                                debug_assert_eq!(underlying.len(), count);

                                let actual = Dope::from(underlying.as_mut_slice());

                                let actual = actual.iter();

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

                            let actual = Dope::from(underlying.as_mut_slice());

                            let mut actual = actual.iter();

                            for expected in (0..256).rev() {
                                _ = actual.next().expect("an element");

                                let (lower, _upper) = actual.size_hint();

                                assert_eq!(lower, expected);
                            }
                        }

                        #[test]
                        fn then_upper_bound_decreases() {
                            let mut underlying: Vec<_> = (0..256).collect();

                            let actual = Dope::from(underlying.as_mut_slice());

                            let mut actual = actual.iter();

                            for expected in (0..256).rev() {
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
                    fn when_empty_then_yields_none() {
                        let mut underlying: [usize; 0] = [];

                        debug_assert!(underlying.is_empty());

                        let actual = Dope::from(underlying.as_mut_slice());

                        let mut actual = actual.iter();

                        assert_eq!(actual.next_back(), None);
                    }

                    mod when_not_empty {
                        use super::*;

                        #[test]
                        fn then_can_be_advanced_count_times() {
                            for length in 1..256 {
                                let mut underlying: Vec<_> = (0..length).collect();

                                debug_assert!(!underlying.is_empty());
                                debug_assert_eq!(underlying.len(), length);

                                let actual = Dope::from(underlying.as_mut_slice());

                                let actual = actual.iter().rev();

                                assert_eq!(actual.count(), length);
                            }
                        }

                        #[test]
                        fn then_yields_correct_elements_in_correct_order() {
                            for length in 1..256 {
                                let mut underlying: Vec<_> = (0..length).collect();
                                let expected = underlying.clone();

                                debug_assert!(!underlying.is_empty());
                                debug_assert_eq!(underlying.len(), length);

                                let actual = Dope::from(underlying.as_mut_slice());

                                let actual = actual.iter().rev();

                                assert!(actual.eq(expected.iter().rev()));
                            }
                        }

                        #[test]
                        fn when_advanced_from_both_ends_then_prevents_yielding_elements_more_than_once() {
                            let mut underlying: Vec<_> = (0..256).collect();

                            for advancements in 1..underlying.len() {
                                let actual = Dope::from(underlying.as_mut_slice());

                                let mut actual = actual.iter();

                                // Advance the iterator from the front that many times.
                                for _ in 0..advancements {
                                    _ = actual.next().expect("an element");
                                }

                                // So can advance from the back only the difference as
                                // any more would require yielding an element already
                                // yielded from the front.
                                assert_eq!(actual.rev().count(), underlying.len() - advancements);
                            }
                        }
                    }
                }

                mod size_hint {
                    use super::*;

                    #[test]
                    fn lower_bound_updates_when_advanced() {
                        const ELEMENTS: usize = 8;

                        let mut underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                        let actual = Dope::from(underlying.as_mut_slice());

                        let mut actual = actual.iter().rev();

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

                        let actual = Dope::from(underlying.as_mut_slice());

                        let mut actual = actual.iter().rev();

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
                fn when_empty_then_continues_to_yield_none() {
                    let mut elements: [usize; 0] = [];

                    let actual = Dope::from(elements.as_mut_slice());

                    let mut actual = actual.iter();

                    // Yields `None` once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }

                mod when_not_empty {
                    use super::*;

                    #[test]
                    fn when_exhausted_from_the_front_then_continues_to_yield_none() {
                        let mut elements = [0];

                        let actual = Dope::from(elements.as_mut_slice());

                        let mut actual = actual.iter();

                        // Exhaust the element.
                        _ = actual.next().expect("the one element");

                        // Yields `None` once.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);

                        // Continues to yield `None`.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }

                    #[test]
                    fn when_exhausted_from_the_back_then_continues_to_yield_none() {
                        let mut elements = [0];

                        let actual = Dope::from(elements.as_mut_slice());

                        let mut actual = actual.iter();

                        // Exhaust the element.
                        _ = actual.next_back().expect("the one element");

                        // Yields `None` once.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);

                        // Continues to yield `None`.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }

                    #[test]
                    fn when_exhausted_from_both_ends_then_continues_to_yield_none() {
                        let mut elements = [0, 0];

                        let actual = Dope::from(elements.as_mut_slice());

                        let mut actual = actual.iter();

                        // Exhaust the element.
                        _ = actual.next().expect("the first element");
                        _ = actual.next_back().expect("the last element");

                        // Yields `None` once.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);

                        // Continues to yield `None`.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }
                }
            }
        }

        mod iter_mut {
            use super::*;

            mod iterator {
                use super::*;

                mod next {
                    use super::*;

                    #[test]
                    fn when_empty_then_yields_none() {
                        let mut underlying: [usize; 0] = [];

                        debug_assert!(underlying.is_empty());

                        let mut actual = Dope::from(underlying.as_mut_slice());

                        let mut actual = actual.iter_mut();

                        assert_eq!(actual.next(), None);
                    }

                    mod when_not_empty {
                        use super::*;

                        #[test]
                        fn then_can_be_advanced_count_times() {
                            for length in 1..256 {
                                let mut underlying: Vec<_> = (0..length).collect();

                                debug_assert!(!underlying.is_empty());
                                debug_assert_eq!(underlying.len(), length);

                                let mut actual = Dope::from(underlying.as_mut_slice());

                                let actual = actual.iter_mut();

                                assert_eq!(actual.count(), length);
                            }
                        }

                        #[test]
                        fn then_yields_correct_elements_in_correct_order() {
                            for length in 1..256 {
                                let mut underlying: Vec<_> = (0..length).collect();
                                let expected = underlying.clone();

                                debug_assert!(!underlying.is_empty());
                                debug_assert_eq!(underlying.len(), length);

                                let mut actual = Dope::from(underlying.as_mut_slice());

                                let actual = actual.iter_mut();

                                assert!(actual.eq(expected.iter()));
                            }
                        }

                        #[test]
                        fn when_yielded_reference_is_mutated_then_underlying_element_is_mutated() {
                            const ELEMENTS: usize = 256;

                            let mut underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                            let mut expected = underlying;
                            expected.reverse();

                            let mut actual = Dope::from(underlying.as_mut_slice());
                            let mut actual = actual.iter_mut();

                            for value in (0..ELEMENTS).rev() {
                                let element = actual.next().expect("an element");

                                *element = value;
                            }

                            drop(actual);

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

                                let mut actual = Dope::from(underlying.as_mut_slice());

                                let actual = actual.iter_mut();

                                let (lower, _upper) = actual.size_hint();

                                assert_eq!(lower, count);
                            }
                        }

                        #[test]
                        fn then_upper_bound_is_count() {
                            for count in 0..256 {
                                let mut underlying: Vec<_> = (0..count).collect();

                                debug_assert_eq!(underlying.len(), count);

                                let mut actual = Dope::from(underlying.as_mut_slice());

                                let actual = actual.iter_mut();

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

                            let mut actual = Dope::from(underlying.as_mut_slice());

                            let mut actual = actual.iter_mut();

                            for expected in (0..256).rev() {
                                _ = actual.next().expect("an element");

                                let (lower, _upper) = actual.size_hint();

                                assert_eq!(lower, expected);
                            }
                        }

                        #[test]
                        fn then_upper_bound_decreases() {
                            let mut underlying: Vec<_> = (0..256).collect();

                            let mut actual = Dope::from(underlying.as_mut_slice());

                            let mut actual = actual.iter_mut();

                            for expected in (0..256).rev() {
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
                    fn when_empty_then_yields_none() {
                        let mut underlying: [usize; 0] = [];

                        debug_assert!(underlying.is_empty());

                        let mut actual = Dope::from(underlying.as_mut_slice());

                        let mut actual = actual.iter_mut();

                        assert_eq!(actual.next_back(), None);
                    }

                    mod when_not_empty {
                        use super::*;

                        #[test]
                        fn then_can_be_advanced_count_times() {
                            for length in 1..256 {
                                let mut underlying: Vec<_> = (0..length).collect();

                                debug_assert!(!underlying.is_empty());
                                debug_assert_eq!(underlying.len(), length);

                                let mut actual = Dope::from(underlying.as_mut_slice());

                                let actual = actual.iter_mut().rev();

                                assert_eq!(actual.count(), length);
                            }
                        }

                        #[test]
                        fn then_yields_correct_elements_in_correct_order() {
                            for length in 1..256 {
                                let mut underlying: Vec<_> = (0..length).collect();
                                let expected = underlying.clone();

                                debug_assert!(!underlying.is_empty());
                                debug_assert_eq!(underlying.len(), length);

                                let mut actual = Dope::from(underlying.as_mut_slice());

                                let actual = actual.iter_mut().rev();

                                assert!(actual.eq(expected.iter().rev()));
                            }
                        }

                        #[test]
                        fn when_yielded_reference_is_mutated_then_underlying_element_is_mutated() {
                            const ELEMENTS: usize = 256;

                            let mut underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                            let mut expected = underlying;
                            expected.reverse();

                            let mut actual = Dope::from(underlying.as_mut_slice());
                            let mut actual = actual.iter_mut().rev();

                            for value in 0..ELEMENTS {
                                let element = actual.next().expect("an element");

                                *element = value;
                            }

                            drop(actual);

                            assert_eq!(underlying, expected);
                        }

                        #[test]
                        fn when_advanced_from_both_ends_then_prevents_yielding_elements_more_than_once() {
                            let mut underlying: Vec<_> = (0..256).collect();

                            for advancements in 1..underlying.len() {
                                let mut actual = Dope::from(underlying.as_mut_slice());

                                let mut actual = actual.iter_mut();

                                // Advance the iterator from the front that many times.
                                for _ in 0..advancements {
                                    _ = actual.next().expect("an element");
                                }

                                // So can advance from the back only the difference as
                                // any more would require yielding an element already
                                // yielded from the front.
                                assert_eq!(actual.rev().count(), underlying.len() - advancements);
                            }
                        }
                    }
                }

                mod size_hint {
                    use super::*;

                    #[test]
                    fn lower_bound_updates_when_advanced() {
                        const ELEMENTS: usize = 8;

                        let mut underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                        let mut actual = Dope::from(underlying.as_mut_slice());

                        let mut actual = actual.iter_mut().rev();

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

                        let mut actual = Dope::from(underlying.as_mut_slice());

                        let mut actual = actual.iter_mut().rev();

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
                fn when_empty_then_continues_to_yield_none() {
                    let mut elements: [usize; 0] = [];

                    let mut actual = Dope::from(elements.as_mut_slice());

                    let mut actual = actual.iter_mut();

                    // Yields `None` once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }

                mod when_not_empty {
                    use super::*;

                    #[test]
                    fn when_exhausted_from_the_front_then_continues_to_yield_none() {
                        let mut elements = [0];

                        let mut actual = Dope::from(elements.as_mut_slice());

                        let mut actual = actual.iter_mut();

                        // Exhaust the element.
                        _ = actual.next().expect("the one element");

                        // Yields `None` once.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);

                        // Continues to yield `None`.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }

                    #[test]
                    fn when_exhausted_from_the_back_then_continues_to_yield_none() {
                        let mut elements = [0];

                        let mut actual = Dope::from(elements.as_mut_slice());

                        let mut actual = actual.iter_mut();

                        // Exhaust the element.
                        _ = actual.next_back().expect("the one element");

                        // Yields `None` once.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);

                        // Continues to yield `None`.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }

                    #[test]
                    fn when_exhausted_from_both_ends_then_continues_to_yield_none() {
                        let mut elements = [0, 0];

                        let mut actual = Dope::from(elements.as_mut_slice());

                        let mut actual = actual.iter_mut();

                        // Exhaust the element.
                        _ = actual.next().expect("the first element");
                        _ = actual.next_back().expect("the last element");

                        // Yields `None` once.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);

                        // Continues to yield `None`.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }
                }
            }
        }
    }

    mod array {
        use super::*;

        mod as_ptr {
            use super::*;

            #[test]
            fn when_underlying_is_empty_then_yields_correct_address() {
                let mut expected: [usize; 0] = [];
                debug_assert!(expected.is_empty());

                let actual = Dope::from(expected.as_mut_slice());

                assert_eq!(actual.as_ptr(), expected.as_ptr());
            }

            #[test]
            fn when_underlying_is_not_empty_then_yields_correct_address() {
                let mut expected = [0, 1, 2, 3, 4, 5];
                debug_assert!(!expected.is_empty());

                let actual = Dope::from(expected.as_mut_slice());

                assert_eq!(actual.as_ptr(), expected.as_ptr());
            }
        }

        mod as_mut_ptr {
            use super::*;

            #[test]
            fn when_underlying_is_empty_then_yields_correct_address() {
                let mut expected: [usize; 0] = [];
                debug_assert!(expected.is_empty());

                let mut actual = Dope::from(expected.as_mut_slice());

                assert_eq!(actual.as_mut_ptr(), expected.as_mut_ptr());
            }

            #[test]
            fn when_underlying_is_not_empty_then_yields_correct_address() {
                let mut expected = [0, 1, 2, 3, 4, 5];
                debug_assert!(!expected.is_empty());

                let mut actual = Dope::from(expected.as_mut_slice());

                assert_eq!(actual.as_mut_ptr(), expected.as_mut_ptr());
            }

            #[test]
            fn when_pointer_is_mutated_then_underlying_element_is_mutated() {
                const ELEMENTS: usize = 8;

                let mut expected = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                let mut actual = expected;
                let mut dope = Dope::from(actual.as_mut_slice());

                for (index, value) in (0..ELEMENTS).rev().enumerate() {
                    let ptr = dope.as_mut_ptr();

                    // We are testing that this is safe.
                    let element = unsafe { ptr.add(index) };

                    // Ideally, this will panic if unowned memory.
                    unsafe {
                        element.write(value);
                    }
                }

                expected.reverse();

                assert_eq!(actual, expected);
            }
        }
    }
}
