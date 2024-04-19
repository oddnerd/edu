//! Implementations of [`Linear`].

pub mod array;
pub mod list;

pub use array::Array;
pub use list::List;

use super::Collection;

/// A [`Collection`] with sequential ordering.
///
/// Implementations of this trait have exactly one (bidirectional) method of
/// iteration. The logical layout of the elements is one dimensional such that
/// the only relationship between elements is they occur 'before' or 'after'
/// one another. This implies each element is associated with a unique
/// identifying [index](`std::ops::IndexMut`) relative to its position. This
/// means starting from the [`Self::first`] element which is defined as always
/// having an index of zero, all other elements can be accessed by incrementing
/// the index up to and including the [`Self::last`] element.
pub trait Linear<'a>: Collection<'a> + std::ops::IndexMut<usize, Output = Self::Element> {
    /// Iterate over the elements by immutable reference.
    fn iter(
        &self,
    ) -> impl DoubleEndedIterator<Item = &'a Self::Element> + ExactSizeIterator + std::iter::FusedIterator;

    /// Iterate over the elements by mutable reference.
    fn iter_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = &'a mut Self::Element>
           + ExactSizeIterator
           + std::iter::FusedIterator;

    /// Obtain an immutable reference to the element at `index`, bounds checked.
    fn at(&self, index: usize) -> Option<&Self::Element> {
        if index < self.count() {
            Some(&self[index])
        } else {
            None
        }
    }

    /// Obtain a mutable reference to the element at `index`, bounds checked.
    fn at_mut(&mut self, index: usize) -> Option<&mut Self::Element> {
        if index < self.count() {
            Some(&mut self[index])
        } else {
            None
        }
    }

    /// Query the element considered to be at the front, the first element.
    fn first(&self) -> Option<&Self::Element> {
        self.at(0)
    }

    /// Query the element considered to be at the back, the last element.
    fn last(&self) -> Option<&Self::Element> {
        self.at(self.count() - 1)
    }

    /// Obtain a reference to the element at the front, the first element.
    fn first_mut(&mut self) -> Option<&mut Self::Element> {
        self.at_mut(0)
    }

    /// Obtain a reference to the element at the back, the last element.
    fn last_mut(&mut self) -> Option<&mut Self::Element> {
        self.at_mut(self.count() - 1)
    }
}
