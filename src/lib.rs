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
        clippy::unwrap_used,
        clippy::expect_used,

        // TODO: struggling to justify this one
        // clippy::assertions_on_result_states,

        // Indexing/slicing inside tests ought to be so obviously within bounds
        // that requiring use of `get` and then unwrapping the result would be
        // unnecessarily verbose. To the extent that invalid bounds may still
        // be used, that code will never be ran in production and it will
        // invoke a panic thusly failing that test until corrected.
        clippy::indexing_slicing
    )
)]

pub mod algorithm;
pub mod structure;
