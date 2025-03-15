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
    /// Utilities for testing dropping.
    pub(crate) mod drop {
        /// Mock type that tracks if it has been dropped.
        #[derive(Debug)]
        pub(crate) struct Mock {
            /// An external counter that is updated when instances are dropped.
            counter: alloc::rc::Rc<core::cell::RefCell<usize>>,
        }

        impl Drop for Mock {
            /// Externally track that this instance was dropped.
            ///
            /// # Performance
            /// This method take O(1) time and consumes O(1) memory.
            fn drop(&mut self) {
                _ = self.counter.replace_with(|old| old.wrapping_add(1));
            }
        }

        impl Mock {
            /// Construct a counter than can be shared across instances.
            ///
            /// # Performance
            /// This method takes O(1) time and consumes O(1) memory.
            pub(crate) fn new_counter() -> alloc::rc::Rc<core::cell::RefCell<usize>> {
                alloc::rc::Rc::new(core::cell::RefCell::new(usize::default()))
            }

            /// Construct a `Mock` that refers to an existing counter.
            ///
            /// # Performance
            /// This method takes O(1) time and consumes O(1) memory.
            pub(crate) fn new(counter: &alloc::rc::Rc<core::cell::RefCell<usize>>) -> Mock {
                Mock { counter: alloc::rc::Rc::clone(counter), }
            }
        }

        #[test]
        fn new_counter_is_zero() {
            let actual = Mock::new_counter();

            assert_eq!(*actual.borrow(), 0);
        }

        #[test]
        fn new_clones_counter() {
            let counter = Mock::new_counter();

            let actual = Mock::new(&counter);

            assert!(alloc::rc::Rc::ptr_eq(&actual.counter, &counter));
        }

        #[test]
        fn increments_counter_when_dropped() {
            let counter = Mock::new_counter();

            drop(Mock::new(&counter));

            assert_eq!(*counter.borrow(), 1);
        }
    }
}
