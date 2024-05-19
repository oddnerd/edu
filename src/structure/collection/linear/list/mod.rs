//! Implementations of [`List`].

use super::Linear;
use super::Collection;

pub mod singly;
pub use singly::Singly;

pub mod doubly;
pub use doubly::Doubly;

/// A modifiable [`Linear`] [`super::Collection`].
///
/// Unlike the base [`Linear`] trait, implementors of [`Self`] provide methods
/// to alter the total [`super::Collection::count`] of elements.
///
/// # Insertion
///
/// * Elements can be placed before [`Linear::first`] via [`Self::prepend`].
/// * Elements can be placed after [`Linear::last`] via [`Self::append`].
/// * Elements can be inserted at any given index via [`Self::insert`].
///
/// # Removal
///
/// * [First](`Linear::first`) can be removed via [`front`](`Self::front`).
/// * [Last](`Linear::last`) can be removed via [`back`](`Self::back`).
/// * Any given index can be removed via [`remove`](`Self::remove`).
/// * Elements can be [`retain`](`Self::retain`) or
///   [`withdraw`](`Self::withdraw`) given a predicate.
/// * An index range can be moved out via [`drain`](`Self::drain`).
/// * All elements can be removed via [`clear`](`Self::clear`).
pub trait List:
    Linear
    + IntoIterator<Item = Self::Element>
    + DoubleEndedIterator<Item = Self::Element>
    + ExactSizeIterator
    + core::iter::FusedIterator
    + Extend<Self::Element>
    + FromIterator<Self::Element>
{
    /// Insert an `element` at `index`.
    ///
    /// The elements `[..index]` remain unmodified whereas elements `[index..]`
    /// are shifted to the right such that they become `[index + 1..]`, and the
    /// element at `index` is the `element` being inserted.
    ///
    /// # Errors
    /// Yields the `element` when it cannot be inserted.
    fn insert(
        &mut self,
        index: usize,
        element: Self::Element,
    ) -> Result<&mut Self::Element, Self::Element>;

    /// Remove the element at `index`, bounds checked.
    ///
    /// The elements at `[..index]` remain unmodified, the element at `index`
    /// is dropped, and the elements `[index + 1..]` are shifted to the left
    /// such that they become `[index..]`.
    fn remove(&mut self, index: usize) -> Option<Self::Element>;

    /// Remove the element at the front, the first element.
    fn front(&mut self) -> Option<Self::Element> {
        self.next()
    }

    /// Remove the element at the back, the last element.
    fn back(&mut self) -> Option<Self::Element> {
        self.next_back()
    }

    /// Insert an element such that it becomes the first.
    ///
    /// # Errors
    /// If cannot insert the element.
    fn prepend(&mut self, element: Self::Element) -> Result<&mut Self::Element, Self::Element> {
        self.insert(0, element)
    }

    /// Insert an element such that is becomes the last.
    ///
    /// # Errors
    /// Yields the `element` when it cannot be inserted.
    fn append(&mut self, element: Self::Element) -> Result<&mut Self::Element, Self::Element> {
        self.insert(self.len(), element)
    }

    /// Remove the elements within a given index `range`.
    fn drain(
        &mut self,
        range: impl core::ops::RangeBounds<usize>,
    ) -> impl DoubleEndedIterator<Item = Self::Element> + ExactSizeIterator;

    /// Remove all elements matching some `predicate`.
    fn withdraw(
        &mut self,
        predicate: impl FnMut(&Self::Element) -> bool,
    ) -> impl DoubleEndedIterator<Item = Self::Element>;

    /// Keep only the elements matching some `predicate`.
    ///
    /// # Errors
    /// Yields the `element` when it cannot be inserted.
    fn retain(&mut self, mut predicate: impl FnMut(&Self::Element) -> bool) {
        self.withdraw(|element| !predicate(element)).for_each(drop);
    }

    /// Drop all elements.
    fn clear(&mut self) {
        (0..self.count()).for_each(|index| drop(self.remove(index)));
    }
}
