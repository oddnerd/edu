//! Hand-written implementations in Rust for personal reference.

// https://doc.rust-lang.org/rustc/lints/listing/allowed-by-default.html
#![warn(
    // Enable all external static analysis warnings.
    clippy::all,

    // Prefer using `core` namespace over `std`.
    clippy::std_instead_of_core,

    // Prefer using `core` namespace over `alloc`.
    clippy::alloc_instead_of_core,

    // Prefer using `alloc` namespace over `std`.
    clippy::std_instead_of_alloc,

    // Prevent `::symbol` for crate local symbols.
    absolute_paths_not_starting_with_crate,

    // Always explicitly state lifetime parameters.
    elided_lifetimes_in_paths,

    // Prefer lifetime requirement on types over instances.
    explicit_outlives_requirements,

    // Prevent using unwinding ABIs thereby allowing callers to abort on panic.
    ffi_unwind_calls,

    // Prevent identifiers being keywords in later editions.
    keyword_idents,

    // Prevent implicitly dropping non-trivial struct before end of scope.
    let_underscore_drop,

    // Prefer explicitly brining macros into scope.
    macro_use_extern_crate,

    // Prevent macros using undeclared variables.
    meta_variable_misuse,

    // Prefer explicitly declaring ABI linkage used.
    missing_abi,

    // Prefer deriving `Copy` when possible.
    missing_copy_implementations,

    // Require public types have debug formatting available.
    missing_debug_implementations,

    // Require documentation for public items.
    missing_docs,

    // Prefer pure ASCII identifiers over full UTF-8 symbols.
    non_ascii_idents,

    // Prefer fully capturing entire variables instead of specific fields.
    rust_2021_incompatible_closure_captures,

    // Prefer modern or-patterns.
    rust_2021_incompatible_or_patterns,

    // Prefer placeholder lifetime when possible.
    single_use_lifetimes,

    // Prefer coercion over explicit cast when possible.
    trivial_casts,

    // Prevent unnecessarily casting integers to the type they already are.
    trivial_numeric_casts,

    // Prevent binding variables to unit type.
    unit_bindings,

    // Prevent public symbols from being unreachable for users of the crate.
    unreachable_pub,

    // Require explicit unsafe block in unsafe functions.
    unsafe_op_in_unsafe_fn,

    // Prevent unstable features being explicitly imported.
    unstable_features,

    // Prevent crate dependencies that are never used.
    unused_crate_dependencies,

    // Prevent naming meaningless lifetimes that are never used.
    unused_lifetimes,

    // Prevent defining `macro_rules` that are never used.
    unused_macro_rules,

    // Prefer using names already in-scope over fully qualified names.
    unused_qualifications,

    // Prefer explicitly handling `Result`.
    unused_results,

    // Prevent variants with large memory disparity.
    variant_size_differences,
)]

pub mod algorithm;
pub mod structure;
