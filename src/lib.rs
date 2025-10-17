//! Implementations in the Rust programming language for educational reference.

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

pub mod algorithm;
pub mod primitive;
pub mod structure;
pub mod system;
pub mod text;

#[cfg(test)]
mod test {}
