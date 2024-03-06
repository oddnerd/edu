//! Implementations of [`Linear`].

pub mod array;

use super::Collection;

/// A [`Collection`] with sequential ordering.
///
/// Implementations of this trait have only one possible method of iteration
/// thus implicitly having an order, even if such ordering represents nothing
/// of the elements. Such [`Collection`] are one-dimensional hence elements can
/// either be 'before' or 'after' another element but no other relationships
/// are inherent in the structure. Moreover, this implies there will exist
/// element(s) that can be said to be the [`Self::first`] and/or [`Self::last`]
/// contained because they are connected to only one other element whereas all
/// other elements are connected to exactly two.
pub trait Linear<'a>: Collection<'a> + std::iter::IntoIterator {
    /// Iterate over the elements by immutable reference.
    fn iter(&self) -> impl std::iter::Iterator<Item = &'a Self::Element>;

    /// Iterate over the elements by mutable reference.
    fn iter_mut(&mut self) -> impl std::iter::Iterator<Item = &'a mut Self::Element>;

    /// Query the element considered to be at the front, the first element.
    fn first(&self) -> Option<&Self::Element>;

    /// Query the element considered to be at the end, the last element.
    fn last(&self) -> Option<&Self::Element>;
}
