//! Iterators over contigious memory buffers of consecutive elements; [`super::Array`].

mod immutable;
pub use immutable::Iter;

mod mutable;
pub use mutable::IterMut;
