//! Iterators over contigious memory buffers of consecutive elements; [`super::Array`].

mod iter;
pub use iter::Iter;

mod itermut;
pub use itermut::IterMut;
