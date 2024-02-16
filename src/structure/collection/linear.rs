//! Linear collections are ones which logically arrange the elements sequentially.

pub mod array;

use super::Collection;

/// A [`Collection`] whose elements are logically arranged sequentially.
pub trait Linear<'a>: Collection<'a> + std::iter::IntoIterator {
    /// Iterate over the elements by immutable reference.
    fn iter(&self) -> impl std::iter::Iterator<Item = &'a Self::Element>;

    /// Iterate over the elements by mutable reference.
    fn iter_mut(&mut self) -> impl std::iter::Iterator<Item = &'a mut Self::Element>;
}
