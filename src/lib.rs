//! An education reference alternative standard library for the Rust programming language.


//! Hand-written implementations in Rust for educational reference.
//!
//! You, dear reader, should not be here. This library should not be depended
//! upon. Contained within is documentation for a hypothetical consumer, one
//! which ought to remain purely hypothetical. Being here nevertheless, please
//! consider using a [`core`] or [`std`] provided implementation, or perhaps
//! fork (copy-and-paste) the particular implementation of intrigue and
//! thenceforth refactor it to better adapt to your particular use-case.
//!
//! This crate is divided into two top-level modules:
//!
//! * [Data Structures][mod@structure]
//! * [Algorithms][mod@algorithm]
//!
//! The utilities provided can generally be broken into three categories:
//!
//! * [`trait`]: Logical representation of a data structure.
//! * [`struct`]: Physical definition of a logical data structure.
//! * [`fn`]: Physical definition of a logical algorithm.

// Disable counter-productive lints within tests.
#![cfg_attr(
    test,
    allow(
        clippy::undocumented_unsafe_blocks,
        reason = "Unsafe code inside tests ought to be so obviously safe such that requiring an explanation would be unnecessarily verbose. To the extent that safety may be genuinely violated without sufficient explanation, it either does not matter within the context of testing since that code will never be ran in production, and/or the testing itself (most likely via dynamic analysis via Miri) will catch it."
    ),
    allow(
        clippy::expect_used,
        reason = "A wrapper failing to contain a value that is expected to exist implies the failure of that test which panicking invokes. Since use of this feature is allowed only within tests, the potential unrecoverable error is the explicit purpose of using it."
    ),
    allow(
        clippy::indexing_slicing,
        reason = "An index being out of expected bounds implies the failure of that test which panicking invokes. Since use of this feature is allowed only within tests, the potential unrecoverable error is the explicit purpose of using it."
    ),
    allow(
        clippy::unit_arg,
        reason = "Generic code is expected to test abnormal types such as zero-sized types, of which the unit type is one. However, for the purpose of consistency across logically similar tests using different types, is is often implicitly constructed via `Default::default()` which this lint prevents. Since use of this feature is allowed only within tests, implicitly constructing the type is the explicit purpose of using it."
    ),
    allow(
        clippy::assertions_on_result_states,
        reason = "Using `unwrap`/`expect` without binding the value obscures the underlying assertion when that is the intent. Since use of this feature is allowed only within tests, implicitly ignoring the value is the explicit purpose of using it."
    ),
)]

// Link against the `alloc` crate so it may be referred to explicitly instead
// of via re-exports from the `std` crate.
extern crate alloc;






// Do not link against the `std` crate, the Rust standard library.
#![no_std]
// Do not implicitly bring anything from the `core` crate into scope.
#![no_implicit_prelude]

// Link against the `alloc` and `core` crates, the two which make up `std`.
extern crate alloc;
extern crate core;







pub mod algorithm;
pub mod structure;

#[cfg(test)]
mod test {
    /// Implementation of types used in the testing of other implementations.
    pub(crate) mod mock {
        /// Type which updates an external counter when dropped.
        #[derive(Debug, Clone)]
        pub(crate) struct DropCounter {
            /// Access to the external counter.
            counter: alloc::rc::Rc<core::cell::RefCell<usize>>,
        }

        impl DropCounter {
            /// Construct a counter than can be shared across instances.
            ///
            /// # Performance
            /// This takes 𝚶(1) time and consumes 𝚶(1) memory.
            pub(crate) fn new_counter() -> alloc::rc::Rc<core::cell::RefCell<usize>> {
                alloc::rc::Rc::new(core::cell::RefCell::new(usize::default()))
            }

            /// Construct a [`Self`] that refers to an existing counter.
            ///
            /// # Performance
            /// This takes 𝚶(1) time and consumes 𝚶(1) memory.
            pub(crate) fn new(counter: &alloc::rc::Rc<core::cell::RefCell<usize>>) -> Self {
                Self {
                    counter: alloc::rc::Rc::clone(counter),
                }
            }
        }

        impl Drop for DropCounter {
            /// Update the counter to track that this instance was dropped.
            ///
            /// # Performance
            /// This take 𝚶(1) time and consumes 𝚶(1) memory.
            fn drop(&mut self) {
                _ = self.counter.replace_with(|old| old.checked_add(1).expect("countably many elements"));
            }
        }

        /// Iterator that provides an untrustworthy size hint.
        #[derive(Debug)]
        pub(crate) struct SizeHint<Iter: Iterator> {
            /// Underlying supply of realized elements.
            pub iterator: Iter,

            /// The hint returned when queried for the number of elements.
            pub size_hint: (usize, Option<usize>),
        }

        impl<Iter: Iterator> Iterator for SizeHint<Iter> {
            /// The type being yielded when iterated.
            type Item = Iter::Item;

            /// Obtain the next realized element, if there is one.
            ///
            /// # Performance
            /// This has the characteristics of the underlying iterator.
            fn next(&mut self) -> Option<Self::Item> {
                self.iterator.next()
            }

            /// Obtain the arbitrary hint for the remaining number of elements.
            ///
            /// # Performance
            /// This takes 𝚶(1) time and consumes 𝚶(1) memory.
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.size_hint
            }
        }

        impl<Iter: Iterator> ExactSizeIterator for SizeHint<Iter> {}

        /// Type that can be default constructed.
        #[derive(Debug, PartialEq, Eq)]
        pub(crate) struct DefaultValue {
            /// The underlying value to be compared against.
            value: usize,
        }

        impl Default for DefaultValue {
            /// Construct an instance.
            ///
            /// # Performance
            /// This takes 𝚶(1) time and consumes 𝚶(1) memory.
            fn default() -> Self {
                DefaultValue {
                    // The purpose of using this mock instead of a raw integer
                    // is because some platforms will zero initialize memory
                    // but the default value for integers is also zero hence
                    // there would be no measurable difference between
                    // correctly using the default constructor for a type or
                    // simply forcibly reading uninitialized memory. This
                    // provides a centralized human-generated value that will
                    // eliminate false positives when testing.
                    value: 31_415_926,
                }
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

                        mod given_no_counters_exist {
                            use super::*;

                            #[test]
                            fn then_is_zero() {
                                let actual = DropCounter::new_counter();

                                assert_eq!(actual.take(), 0);
                            }
                        }

                        mod given_another_counter_exists {
                            use super::*;

                            #[test]
                            fn then_is_distinct() {
                                let first = DropCounter::new_counter();
                                let second = DropCounter::new_counter();

                                assert_ne!(first.as_ptr(), second.as_ptr());
                            }
                        }
                    }

                    mod new {
                        use super::*;

                        mod given_a_counter_with_some_value {
                            use super::*;

                            #[test]
                            fn then_references_counter() {
                                for value in 0..32 {
                                    let counter = DropCounter::new_counter();

                                    _ = counter.replace(value);

                                    let actual = DropCounter::new(&counter);

                                    assert_eq!(actual.counter.as_ptr(), counter.as_ptr());
                                }
                            }

                            #[test]
                            fn then_does_not_mutate_counter() {
                                for value in 0..32 {
                                    let counter = DropCounter::new_counter();

                                    _ = counter.replace(value);

                                    let _actual = DropCounter::new(&counter);

                                    assert_eq!(counter.take(), value);
                                }
                            }
                        }
                    }
                }

                mod drop {
                    use super::*;

                    mod given_an_instance {
                        use super::*;

                        #[test]
                        fn then_increments_counter() {
                            let counter = DropCounter::new_counter();

                            drop(DropCounter::new(&counter));

                            assert_eq!(counter.take(), 1);
                        }
                    }

                    mod given_multiple_instances_with_different_counters {
                        use super::*;

                        #[test]
                        fn then_does_not_mutate_other_counters() {
                            let first = DropCounter::new_counter();
                            let second = DropCounter::new_counter();

                            drop(DropCounter::new(&first));

                            assert_eq!(second.take(), 0);
                        }
                    }

                    mod given_multiple_instances_with_the_same_counter {
                        use super::*;

                        mod when_all_dropped {
                            use super::*;

                            #[test]
                            fn then_counter_is_number_of_instances() {
                                for expected in 2..32 {
                                    let counter = DropCounter::new_counter();

                                    let instances: Vec<_> = core::iter::repeat_n(DropCounter::new(&counter), expected).collect();

                                    drop(instances);

                                    assert_eq!(counter.take(), expected);
                                }
                            }
                        }

                        mod when_only_some_dropped {
                            use super::*;

                            #[test]
                            fn then_counter_is_how_many_have_been_dropped() {
                                for instances in 2..32 {
                                    for dropped in 1..instances {
                                        let counter = DropCounter::new_counter();

                                        let mut instances: Vec<_> = core::iter::repeat_n(DropCounter::new(&counter), instances).collect();

                                        instances.drain(0..dropped).for_each(drop);

                                        assert_eq!(counter.take(), dropped);
                                    }
                                }
                            }
                        }
                    }
                }
            }

            mod size_hint {
                use super::*;

                mod iterator {
                    use super::*;

                    mod next {
                        use super::*;

                        mod given_empty_underlying_iterator {
                            use super::*;

                            #[test]
                            fn then_is_none() {
                                let mut actual = SizeHint {
                                    iterator: core::iter::empty::<usize>(),
                                    size_hint: (0, None)
                                };

                                assert!(actual.next().is_none());
                            }

                            #[test]
                            fn then_does_not_mutate_size_hint() {
                                let mut actual = SizeHint {
                                    iterator: core::iter::empty::<usize>(),
                                    size_hint: (0, None)
                                };

                                _ = actual.next();

                                assert_eq!(actual.size_hint, (0, None));
                            }
                        }

                        mod given_not_empty_underlying_iterator {
                            use super::*;

                            #[test]
                            fn then_is_element() {
                                for elements in 1..32 {
                                    for advances in 0..elements {
                                        let mut actual = SizeHint {
                                            iterator: 0..elements,
                                            size_hint: (0, None),
                                        };

                                        actual.by_ref().take(advances).for_each(drop);

                                        assert_eq!(actual.next(), Some(advances));
                                    }
                                }
                            }

                            #[test]
                            fn then_does_not_mutate_size_hint() {
                                for elements in 1..32 {
                                    for advances in 0..elements {
                                        let mut actual = SizeHint {
                                            iterator: 0..elements,
                                            size_hint: (0, None),
                                        };

                                        actual.by_ref().take(advances).for_each(drop);

                                        _ = actual.next();

                                        assert_eq!(actual.size_hint, (0, None));
                                    }
                                }
                            }
                        }

                        mod given_not_empty_but_exhausted_underlying_iterator {
                            use super::*;

                            #[test]
                            fn then_is_none() {}

                            #[test]
                            fn then_does_not_mutate_size_hint() {}
                        }
                    }

                    mod size_hint {
                        use super::*;

                        mod given_empty_underlying_iterator {}

                        mod given_not_empty_underlying_iterator {}

                        mod given_not_empty_but_exhausted_underlying_iterator {}
                    }






                    #[test]
                    fn when_advanced_then_advances_underlying_iterator() {
                        for elements in 0..32 {
                            let expected: Vec<_> = (0..elements).collect();

                            let actual = SizeHint {
                                iterator: expected.iter().copied(),
                                size_hint: (usize::default(), Some(usize::default())),
                            };

                            assert!(actual.eq(0..elements));
                        }
                    }

                    #[test]
                    fn when_size_hint_upper_is_none_then_is_custom_value() {
                        for elements in 0..32 {
                            for lower in 0..32 {
                                let expected: Vec<_> = (0..elements).collect();

                                let actual = SizeHint {
                                    iterator: expected.iter().copied(),
                                    size_hint: (lower, None),
                                };

                                assert_eq!(actual.size_hint(), (lower, None));
                            }
                        }
                    }

                    #[test]
                    fn when_size_hint_upper_is_some_then_is_custom_value() {
                        for elements in 0..32 {
                            for lower in 0..32 {
                                for upper in 0..32 {
                                    let expected: Vec<_> = (0..elements).collect();

                                    let actual = SizeHint {
                                        iterator: expected.iter().copied(),
                                        size_hint: (lower, Some(upper)),
                                    };

                                    assert_eq!(actual.size_hint(), (lower, Some(upper)));
                                }
                            }
                        }
                    }
                }

                mod exact_size_iterator {
                    use super::*;

                    mod len {
                        use super::*;
                    }
                }
            }

            mod default_value {
                use super::*;

                mod default {
                    use super::*;

                    #[test]
                    fn then_is_custom_value() {
                        let actual = DefaultValue::default();

                        assert_eq!(actual.value, 31_415_926);
                    }
                }
            }
        }
    }
}
