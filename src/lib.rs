//! Hand-written implementations in Rust for personal reference.

// Disable counter-productive lints within tests.
#![cfg_attr(
    test,
    allow(
        // Unsafe code inside tests ought to be so obviously safe such that
        // requiring an explanation would be unnecessarily verbose. To the
        // extent that safety may be genuinely violated without sufficient
        // explanation, it either does not matter within the context of testing
        // since that code will never be ran in production, and/or the testing
        // itself (most likely dynamic analysis via Miri) will catch it.
        clippy::undocumented_unsafe_blocks,

        // A wrapper failing to contain a value that is expected to exist
        // implies the failure of that test which panicking invokes. Since
        // use of this feature is allowed only within tests, the potential
        // unrecoverable error is the explicit purpose of using it.
        clippy::expect_used,

        // An index being out of expected bounds implies the failure of that
        // test which panicking invokes. Since use of this feature is allowed
        // only within tests, the potential unrecoverable error is the explicit
        // purpose of using it.
        clippy::indexing_slicing
    )
)]

// Explicitly link against the `alloc` crate.
extern crate alloc;

pub mod algorithm;
pub mod structure;

#[cfg(test)]
mod test {
    /// Types which implement interfaces with behaviour for testing purposes.
    pub(crate) mod mock {
        /// Mock element that updates an external counter when dropped.
        #[derive(Debug)]
        pub(crate) struct DropCounter {
            /// Access to the external counter.
            counter: alloc::rc::Rc<core::cell::RefCell<usize>>,
        }

        impl DropCounter {
            /// Construct a counter than can be shared across instances.
            ///
            /// # Performance
            /// This method takes O(1) time and consumes O(1) memory.
            pub(crate) fn new_counter() -> alloc::rc::Rc<core::cell::RefCell<usize>> {
                alloc::rc::Rc::new(core::cell::RefCell::new(usize::default()))
            }

            /// Construct a [`Self`] that refers to an existing counter.
            ///
            /// # Performance
            /// This method takes O(1) time and consumes O(1) memory.
            pub(crate) fn new(counter: &alloc::rc::Rc<core::cell::RefCell<usize>>) -> Self {
                Self { counter: alloc::rc::Rc::clone(counter), }
            }
        }

        impl Drop for DropCounter {
            /// Externally track that this instance was dropped.
            ///
            /// # Performance
            /// This method take O(1) time and consumes O(1) memory.
            fn drop(&mut self) {
                _ = self.counter.replace_with(|old| old.wrapping_add(1));
            }
        }

        /// Mock iterator that provides an erroneously large size hint.
        #[derive(Debug)]
        pub (crate) struct SizeHint<I> {
            /// Underlying supply of genuine elements.
            pub data: core::iter::Copied<I>,

            /// The hint returned when queried for the number of elements.
            pub size_hint: (usize, Option<usize>),
        }

        impl<'a, T: 'a + Copy, I: Iterator<Item = &'a T>> Iterator for SizeHint<I> {
            /// The type being yielded when iterated.
            type Item = T;

            /// Obtain the next genuine element, if there is one.
            ///
            /// # Performance
            /// This method has the characteristics of the underlying iterator.
            fn next(&mut self) -> Option<Self::Item> {
                self.data.next()
            }

            /// Obtain the faulty hint for the remaining number of elements.
            ///
            /// # Performance
            /// This method takes O(1) time and consumes O(1) memory.
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.size_hint
            }
        }

        mod test {
            use super::*;

            mod drop_counter {
                use super::*;

                mod method {
                    use super::*;

                    mod new_counter {
                        use super::*;

                        #[test]
                        fn is_zero() {
                            let actual = DropCounter::new_counter();

                            assert_eq!(actual.take(), 0);
                        }
                    }

                    mod new {
                        use super::*;

                        #[test]
                        fn clones_counter() {
                            let counter = DropCounter::new_counter();

                            let actual = DropCounter::new(&counter);

                            assert!(alloc::rc::Rc::ptr_eq(&actual.counter, &counter));
                        }
                    }
                }

                mod drop {
                    use super::*;

                    #[test]
                    fn increments_counter() {
                        let counter = DropCounter::new_counter();

                        drop(DropCounter::new(&counter));

                        assert_eq!(counter.take(), 1);
                    }
                }
            }

            mod size_hint {
                use super::*;

                mod iterator {
                    use super::*;

                    #[test]
                    fn yields_elements() {
                        let expected = [0, 1, 2, 3, 4, 5];

                        let actual = SizeHint {
                            data: expected.iter().copied(),
                            size_hint: (usize::default(), Some(usize::default())),
                        };

                        assert!(actual.eq(expected));
                    }

                    #[test]
                    fn hint_is_custom_value() {
                        let expected = [0, 1, 2, 3, 4, 5];

                        let actual = SizeHint {
                            data: expected.iter().copied(),
                            size_hint: (12345, None),
                        };

                        assert_eq!(actual.size_hint(), (12345, None));
                    }
                }
            }
        }
    }
}
