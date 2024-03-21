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
pub trait Linear<'a>: Collection<'a> + std::ops::IndexMut<usize, Output = Self::Element> {
    /// Iterate over the elements by immutable reference.
    fn iter(&self) -> impl std::iter::Iterator<Item = &'a Self::Element>;

    /// Iterate over the elements by mutable reference.
    fn iter_mut(&mut self) -> impl std::iter::Iterator<Item = &'a mut Self::Element>;

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

    /// Obtain a reference to the element at the back, the last element().
    fn last_mut(&mut self) -> Option<&mut Self::Element> {
        self.at_mut(self.count() - 1)
    }
}

/// [`Linear`] [`Collection`] which can insert or remove elements.
pub trait LinearMut<'a>: Linear<'a> + std::iter::IntoIterator<Item = Self::Element> {
    /// Insert an element at `index`.
    ///
    /// The elements `[..index]` remain unmodified, whereas elements `[index..]`
    /// are shifted to the right such that they become `[index + 1..]`, and the
    /// element at `index` is the `element` being inserted.
    fn insert(&mut self, index: usize, element: Self::Element) -> Result<&mut Self::Element, Self::Element>;

    /// Remove the element at `index`.
    ///
    /// The elements at `[..index]` remain unmodified, the element at `index`
    /// is dropped, and the elements `[index + 1..]` are shifted to the left
    /// such that they become `[index..]`.
    fn remove(&mut self, index: usize) -> Option<Self::Element>;

    /// Remove the element at the front, the first element.
    fn front(&mut self) -> Option<Self::Element> {
        self.remove(0)
    }

    /// Remove the element at the back, the last element.
    fn back(&mut self) -> Option<Self::Element> {
        self.remove(self.count() - 1)
    }

    /// Insert an element such that it becomes the first.
    fn prepend(&mut self, element: Self::Element) -> Result<&mut Self::Element, Self::Element> {
        self.insert(0, element)
    }

    /// Insert an element such that is becomes the last.
    fn append(&mut self, element: Self::Element) -> Result<&mut Self::Element, Self::Element> {
        self.insert(self.count(), element)
    }
}
