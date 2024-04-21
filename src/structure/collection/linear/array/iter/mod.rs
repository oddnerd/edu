//! Iterators over [`Array`](`super::Array`).

mod immutable;
pub(super) use immutable::Iter;

mod mutable;
pub(super) use mutable::IterMut;
