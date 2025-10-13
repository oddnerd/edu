//! An educational reference alternative standard library for Rust.
//!
//! This crate provides an alternative standard library for the Rust
//! programming language. It is dependency[^1] free, intended to provide
//! portable utilities implementing core computer science concepts.
//!
//! [^1]: Because some aspects of the Rust standard library rely upon compiler
//!       intrinsics for which this crate does not have access to, this does
//!       nevertheless link against the `core` and `alloc` crates.

// Disable counter-productive lints within tests.
#![cfg_attr(
    test,
    allow(
        clippy::undocumented_unsafe_blocks,
        reason = "Unsafe code inside tests ought to be so obviously safe such that requiring an explanation would be unnecessarily verbose. To the extent that safety may be genuinely violated without sufficient explanation, it either does not matter within the context of testing since that code will never be ran in production, and/or the testing itself (most likely via dynamic analysis via Miri) will catch it."
    ),
    allow(
        clippy::unit_arg,
        reason = "Generic code is expected to test abnormal types such as zero-sized types, of which the unit type is one. However, for the purpose of consistency across logically similar tests using different types, is is often implicitly constructed via `Default::default()` which this lint prevents. Since use of this feature is allowed only within tests, implicitly constructing the type is the explicit purpose of using it."
    ),
    allow(
        clippy::assertions_on_result_states,
        reason = "Using `unwrap`/`expect` without binding the value obscures the underlying assertion when that is the intent. Since use of this feature is allowed only within tests, implicitly ignoring the value is the explicit purpose of using it."
    )
)]
// Do not link against the `std` crate, the Rust standard library.
#![no_std]
// Do not implicitly bring anything from the `core` crate into scope.
#![no_implicit_prelude]

// Link against the `alloc` and `core` crates, the two which make up `std`.
extern crate alloc;
extern crate core;

#[cfg(test)]
mod test {}
