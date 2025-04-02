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
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(N) | 𝛀(N) | 𝚯(N) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(N) | 𝛀(N) | 𝚯(N) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(N) | 𝛀(N) | 𝚯(N) |
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
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
    /// #### Time Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
    ///
    /// #### Memory Complexity
    /// | Worst | Best | Average |
    /// | :-: | :-: | :-: |
    /// | O(1) | 𝛀(1) | 𝚯(1) |
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
        fn is_symmetric() {
            // a == b <=> b == a

            let elements = [0, 1, 2, 3, 4, 5];

            let mut a = elements;
            let a = Dope::from(a.as_mut_slice());

            let mut b = elements;
            let b = Dope::from(b.as_mut_slice());

            assert_eq!(a, b);
            assert_eq!(b, a);
        }

        #[test]
        fn is_transitive() {
            // a == b && b == c <=> a == c

            let elements = [0, 1, 2, 3, 4, 5];

            let mut a = elements;
            let a = Dope::from(a.as_mut_slice());

            let mut b = elements;
            let b = Dope::from(b.as_mut_slice());

            let mut c = elements;
            let c = Dope::from(c.as_mut_slice());

            assert_eq!(a, b);
            assert_eq!(b, c);
            assert_eq!(a, c);
        }

        #[test]
        fn is_equal_when_same_elements_in_same_order() {
            const ELEMENTS: usize = 8;

            let elements = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            for end in 1..ELEMENTS {
                let mut a = elements;
                let a = Dope::from(&mut a[..end]);

                let mut b = elements;
                let b = Dope::from(&mut b[..end]);

                assert_eq!(a, b);
            }
        }

        #[test]
        fn is_equal_when_both_underlyings_are_empty() {
            let elements: [usize; 0] = [];
            debug_assert!(elements.is_empty());

            let mut a = elements;
            let a = Dope::from(a.as_mut_slice());

            let mut b = elements;
            let b = Dope::from(b.as_mut_slice());

            assert_eq!(a, b);
        }

        #[test]
        fn is_not_equal_when_same_elements_in_different_order() {
            const ELEMENTS: usize = 8;

            let elements = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            let mut a = elements;
            let a = Dope::from(a.as_mut_slice());

            for offset in 1..ELEMENTS {
                let mut b = elements;
                b.rotate_right(offset);
                let b = Dope::from(b.as_mut_slice());

                assert_ne!(a, b);
            }
        }

        #[test]
        fn is_not_equal_when_an_element_has_a_different_value() {
            const ELEMENTS: usize = 8;

            let elements = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            let mut a = elements;
            let a = Dope::from(a.as_mut_slice());

            for index in 0..ELEMENTS {
                let mut b = elements;

                b[index] = 12345; // Some arbitrary distinct value.

                let b = Dope::from(b.as_mut_slice());

                assert_ne!(a, b);
            }
        }

        #[test]
        fn is_not_equal_when_different_lengths_but_equal_subset() {
            const ELEMENTS: usize = 8;

            let elements = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            let mut a = elements;
            let a = Dope::from(a.as_mut_slice());

            for end in 1..ELEMENTS {
                let mut b = elements;
                let b = &mut b[..end];

                debug_assert_eq!(&elements[..end], b);

                let b = Dope::from(b);

                assert_ne!(a, b);
            }
        }
    }

    mod equality {
        use super::*;

        #[test]
        fn is_reflexive() {
            // a == a

            let mut elements = [0, 1, 2, 3, 4, 5];

            let a = Dope::from(elements.as_mut_slice());

            assert_eq!(a, a);
        }
    }

    mod index {
        use super::*;

        use core::ops::Index as _;

        #[test]
        #[should_panic = "index out of bounds"]
        fn panics_when_indexing_into_empty_underlying() {
            let mut underlying: [usize; 0] = [];

            let instance = Dope::from(underlying.as_mut_slice());

            _ = instance.index(0);
        }

        #[test]
        #[should_panic = "index out of bounds"]
        fn panics_when_index_is_out_of_bounds() {
            let mut underlying = [0, 1, 2, 3, 4, 5];

            let instance = Dope::from(underlying.as_mut_slice());

            _ = instance.index(6);
        }

        #[test]
        fn yields_correct_element_when_index_is_inside_bounds() {
            const ELEMENTS: usize = 8;

            let underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            #[expect(clippy::needless_range_loop, reason = "explicitly testing index")]
            for index in 0..ELEMENTS {
                assert_eq!(underlying.index(index), &index);
            }
        }
    }

    mod index_mut {
        use super::*;

        use core::ops::IndexMut as _;

        #[test]
        #[should_panic = "index out of bounds"]
        fn panics_when_indexing_into_empty_underlying() {
            let mut underlying: [usize; 0] = [];

            let mut instance = Dope::from(underlying.as_mut_slice());

            _ = instance.index_mut(0);
        }

        #[test]
        #[should_panic = "index out of bounds"]
        fn panics_when_index_is_out_of_bounds() {
            let mut underlying = [0, 1, 2, 3, 4, 5];

            let mut instance = Dope::from(underlying.as_mut_slice());

            _ = instance.index_mut(6);
        }

        #[test]
        fn yields_correct_element_when_index_is_inside_bounds() {
            const ELEMENTS: usize = 8;

            let mut underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            #[expect(clippy::needless_range_loop, reason = "explicitly testing index")]
            for index in 0..ELEMENTS {
                assert_eq!(underlying.index_mut(index), &index);
            }
        }

        #[test]
        fn underlying_element_is_updated_when_yielded_reference_is_mutated() {
            const ELEMENTS: usize = 8;

            let mut expected = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

            let mut actual = expected;
            let mut instance = Dope::from(actual.as_mut_slice());

            for (index, value) in (0..ELEMENTS).rev().enumerate() {
                *instance.index_mut(index) = value;
            }

            expected.reverse();

            assert_eq!(actual, expected);
        }
    }

    mod debug {
        use super::*;

        #[test]
        fn is_an_empty_list_when_underlying_is_empty() {
            let expected: [usize; 0] = [];
            debug_assert!(expected.is_empty());

            let mut underlying = expected;
            let actual = Dope::from(underlying.as_mut_slice());

            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        }

        #[test]
        fn is_a_list_of_the_correct_elements_in_the_correct_order_when_underlying_is_not_empty() {
            let expected = [0, 1, 2, 3, 4, 5];

            let mut underlying = expected;
            let actual = Dope::from(underlying.as_mut_slice());

            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        }
    }

    mod collection {
        use super::*;

        mod count {
            use super::*;

            #[test]
            fn is_zero_when_underlying_is_empty() {
                let mut underlying: [usize; 0] = [];
                debug_assert!(underlying.is_empty());

                let actual = Dope::from(underlying.as_mut_slice());

                assert_eq!(actual.count(), 0);
            }

            #[test]
            fn is_number_of_elements_when_underlying_is_not_empty() {
                const ELEMENTS: usize = 8;

                let mut underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);
                debug_assert!(!underlying.is_empty());

                for count in 1..=ELEMENTS {
                    let actual = Dope::from(&mut underlying[..count]);

                    assert_eq!(actual.count(), count);
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
                    fn yields_none_when_underlying_is_empty() {
                        let mut underlying: [usize; 0] = [];
                        debug_assert!(underlying.is_empty());

                        let actual = Dope::from(underlying.as_mut_slice());
                        let mut actual = actual.iter();

                        assert_eq!(actual.next(), None);
                    }

                    #[test]
                    fn can_be_advanced_the_number_of_elements_when_underlying_is_not_empty() {
                        let expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let mut actual = expected;
                        let actual = Dope::from(actual.as_mut_slice());
                        let actual = actual.iter();

                        assert_eq!(actual.count(), expected.len());
                    }

                    #[test]
                    fn yields_correct_elements_in_correct_order_when_underlying_is_not_empty() {
                        let expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let mut actual = expected;
                        let actual = Dope::from(actual.as_mut_slice());
                        let actual = actual.iter();

                        assert!(actual.eq(expected.iter()));
                    }
                }

                mod size_hint {
                    use super::*;

                    #[test]
                    fn lower_bound_is_number_of_elements_when_constructed() {
                        let expected = [0, 1, 2, 3, 4, 5];

                        let mut actual = expected;
                        let actual = Dope::from(actual.as_mut_slice());
                        let actual = actual.iter();

                        let (lower, _upper) = actual.size_hint();

                        assert_eq!(lower, expected.len());
                    }

                    #[test]
                    fn lower_bound_updates_when_advanced() {
                        const ELEMENTS: usize = 8;

                        let mut underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                        let actual = Dope::from(underlying.as_mut_slice());
                        let mut actual = actual.iter();

                        for expected in (0..ELEMENTS).rev() {
                            _ = actual.next().expect("an element");

                            let (lower, _upper) = actual.size_hint();

                            assert_eq!(lower, expected);
                        }
                    }

                    #[test]
                    fn upper_bound_is_number_of_elements_when_constructed() {
                        let expected = [0, 1, 2, 3, 4, 5];

                        let mut actual = expected;
                        let actual = Dope::from(actual.as_mut_slice());
                        let actual = actual.iter();

                        let (_lower, upper) = actual.size_hint();

                        assert_eq!(upper, Some(expected.len()));
                    }

                    #[test]
                    fn upper_bound_updates_when_advanced() {
                        const ELEMENTS: usize = 8;

                        let mut underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                        let actual = Dope::from(underlying.as_mut_slice());
                        let mut actual = actual.iter();

                        for expected in (0..ELEMENTS).rev() {
                            _ = actual.next().expect("an element");

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
                        let mut underlying: [usize; 0] = [];
                        debug_assert!(underlying.is_empty());

                        let actual = Dope::from(underlying.as_mut_slice());
                        let mut actual = actual.iter().rev();

                        assert_eq!(actual.next(), None);
                    }

                    #[test]
                    fn can_be_advanced_the_number_of_elements_when_underlying_is_not_empty() {
                        let expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let mut actual = expected;
                        let actual = Dope::from(actual.as_mut_slice());
                        let actual = actual.iter().rev();

                        assert_eq!(actual.count(), expected.len());
                    }

                    #[test]
                    fn yields_correct_elements_in_correct_order_when_underlying_is_not_empty() {
                        let expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let mut actual = expected;
                        let actual = Dope::from(actual.as_mut_slice());
                        let actual = actual.iter().rev();

                        assert!(actual.eq(expected.iter().rev()));
                    }

                    #[test]
                    fn prevents_elements_from_being_yielded_more_than_once_when_advanced_from_both_ends()
                     {
                        let mut underlying = [0, 1];
                        debug_assert!(!underlying.is_empty());

                        let actual = Dope::from(underlying.as_mut_slice());
                        let mut actual = actual.iter();

                        _ = actual.next().expect("consumes element with value 0");
                        _ = actual.next_back().expect("consumes element with value 1");

                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
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
                fn continues_to_yield_none_when_underlying_is_empty() {
                    let mut underlying: [usize; 0] = [];
                    debug_assert!(underlying.is_empty());

                    let actual = Dope::from(underlying.as_mut_slice());
                    let mut actual = actual.iter();

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

                    let actual = Dope::from(underlying.as_mut_slice());
                    let mut actual = actual.iter();

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

        mod iter_mut {
            use super::*;

            mod iterator {
                use super::*;

                mod next {
                    use super::*;

                    #[test]
                    fn yields_none_when_underlying_is_empty() {
                        let mut underlying: [usize; 0] = [];
                        debug_assert!(underlying.is_empty());

                        let mut actual = Dope::from(underlying.as_mut_slice());
                        let mut actual = actual.iter_mut();

                        assert_eq!(actual.next(), None);
                    }

                    #[test]
                    fn can_be_advanced_the_number_of_elements_when_underlying_is_not_empty() {
                        let expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let mut actual = expected;
                        let mut actual = Dope::from(actual.as_mut_slice());
                        let actual = actual.iter_mut();

                        assert_eq!(actual.count(), expected.len());
                    }

                    #[test]
                    fn yields_correct_elements_in_correct_order_when_underlying_is_not_empty() {
                        let mut expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let mut actual = expected;
                        let mut actual = Dope::from(actual.as_mut_slice());
                        let actual = actual.iter_mut();

                        assert!(actual.eq(expected.iter_mut()));
                    }

                    #[test]
                    fn underlying_element_is_updated_when_yielded_reference_is_mutated() {
                        const ELEMENTS: usize = 8;

                        let mut actual = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                        let mut expected = actual;
                        expected.reverse();

                        let mut dope = Dope::from(actual.as_mut_slice());
                        let mut iter = dope.iter_mut();

                        for value in (0..ELEMENTS).rev() {
                            let element = iter.next().expect("an element");

                            *element = value;
                        }

                        drop(iter);

                        assert_eq!(actual, expected);
                    }
                }

                mod size_hint {
                    use super::*;

                    #[test]
                    fn lower_bound_is_number_of_elements_when_constructed() {
                        let expected = [0, 1, 2, 3, 4, 5];

                        let mut actual = expected;
                        let mut actual = Dope::from(actual.as_mut_slice());
                        let actual = actual.iter_mut();

                        let (lower, _upper) = actual.size_hint();

                        assert_eq!(lower, expected.len());
                    }

                    #[test]
                    fn lower_bound_updates_when_advanced() {
                        const ELEMENTS: usize = 8;

                        let mut underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                        let mut actual = Dope::from(underlying.as_mut_slice());
                        let mut actual = actual.iter_mut();

                        for expected in (0..ELEMENTS).rev() {
                            _ = actual.next().expect("an element");

                            let (lower, _upper) = actual.size_hint();

                            assert_eq!(lower, expected);
                        }
                    }

                    #[test]
                    fn upper_bound_is_number_of_elements_when_constructed() {
                        let expected = [0, 1, 2, 3, 4, 5];

                        let mut actual = expected;
                        let mut actual = Dope::from(actual.as_mut_slice());
                        let actual = actual.iter_mut();

                        let (_lower, upper) = actual.size_hint();

                        assert_eq!(upper, Some(expected.len()));
                    }

                    #[test]
                    fn upper_bound_updates_when_advanced() {
                        const ELEMENTS: usize = 8;

                        let mut underlying = core::array::from_fn::<_, ELEMENTS, _>(|index| index);

                        let mut actual = Dope::from(underlying.as_mut_slice());
                        let mut actual = actual.iter_mut();

                        for expected in (0..ELEMENTS).rev() {
                            _ = actual.next().expect("an element");

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
                        let mut underlying: [usize; 0] = [];
                        debug_assert!(underlying.is_empty());

                        let mut actual = Dope::from(underlying.as_mut_slice());
                        let mut actual = actual.iter_mut().rev();

                        assert_eq!(actual.next(), None);
                    }

                    #[test]
                    fn can_be_advanced_the_number_of_elements_when_underlying_is_not_empty() {
                        let expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let mut actual = expected;
                        let mut actual = Dope::from(actual.as_mut_slice());
                        let actual = actual.iter_mut().rev();

                        assert_eq!(actual.count(), expected.len());
                    }

                    #[test]
                    fn yields_correct_elements_in_correct_order_when_underlying_is_not_empty() {
                        let expected = [0, 1, 2, 3, 4, 5];
                        debug_assert!(!expected.is_empty());

                        let mut actual = expected;
                        let mut actual = Dope::from(actual.as_mut_slice());
                        let actual = actual.iter_mut().rev();

                        assert!(actual.eq(expected.iter().rev()));
                    }

                    #[test]
                    fn prevents_elements_from_being_yielded_more_than_once_when_advanced_from_both_ends()
                     {
                        let mut underlying = [0, 1];
                        debug_assert!(!underlying.is_empty());

                        let mut actual = Dope::from(underlying.as_mut_slice());
                        let mut actual = actual.iter_mut();

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

                        let mut dope = Dope::from(actual.as_mut_slice());
                        let mut iter = dope.iter_mut().rev();

                        for value in 0..ELEMENTS {
                            let element = iter.next().expect("an element");

                            *element = value;
                        }

                        drop(iter);

                        assert_eq!(actual, expected);
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
                fn continues_to_yield_none_when_underlying_is_empty() {
                    let mut underlying: [usize; 0] = [];
                    debug_assert!(underlying.is_empty());

                    let mut actual = Dope::from(underlying.as_mut_slice());
                    let mut actual = actual.iter_mut();

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

                    let mut actual = Dope::from(underlying.as_mut_slice());
                    let mut actual = actual.iter_mut();

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

    mod array {
        use super::*;

        mod as_ptr {
            use super::*;

            #[test]
            fn is_correct_address_when_underlying_is_empty() {
                let mut expected: [usize; 0] = [];
                debug_assert!(expected.is_empty());

                let actual = Dope::from(expected.as_mut_slice());

                assert_eq!(actual.as_ptr(), expected.as_ptr());
            }

            #[test]
            fn is_correct_address_when_underlying_is_not_empty() {
                let mut expected = [0, 1, 2, 3, 4, 5];
                debug_assert!(!expected.is_empty());

                let actual = Dope::from(expected.as_mut_slice());

                assert_eq!(actual.as_ptr(), expected.as_ptr());
            }
        }

        mod as_mut_ptr {
            use super::*;

            #[test]
            fn is_correct_address_when_underlying_is_empty() {
                let mut expected: [usize; 0] = [];
                debug_assert!(expected.is_empty());

                let mut actual = Dope::from(expected.as_mut_slice());

                assert_eq!(actual.as_mut_ptr(), expected.as_mut_ptr());
            }

            #[test]
            fn is_correct_address_when_underlying_is_not_empty() {
                let mut expected = [0, 1, 2, 3, 4, 5];
                debug_assert!(!expected.is_empty());

                let mut actual = Dope::from(expected.as_mut_slice());

                assert_eq!(actual.as_mut_ptr(), expected.as_mut_ptr());
            }

            #[test]
            fn underlying_element_is_updated_when_yielded_pointer_is_mutated() {
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
