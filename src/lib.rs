//! Hand-written implementations in Rust for personal reference.

// Disable particularly aggressive lints exclusively for tests.
#![cfg_attr(
    test,
    allow(
        clippy::undocumented_unsafe_blocks,
        clippy::unwrap_used,
        clippy::expect_used,
        clippy::assertions_on_result_states,
        clippy::indexing_slicing
    )
)]

pub mod algorithm;
pub mod structure;
