//! Implementations of [`Stack`].

use super::Collection;
use super::Linear;

/// A [`Linear`] [`Collection`] with last-in-first-out (LIFO) semantics.
///
/// Elements are physically ordered by the relative insertion order and
/// accessed in that order such that elements can be [`Self::pop`]ped removing
/// an element at a time from most to least recently inserted by
/// [`Self::push`]ing.
///
/// See also: [Wikipedia](https://en.wikipedia.org/wiki/Stack_(abstract_data_type)).
pub trait Stack: Collection + Linear {
    /// Add a new element at the top of the stack.
    ///
    /// # Errors
    /// Yields the `element` when it cannot be inserted.
    fn push(&mut self, element: Self::Element) -> Result<&mut Self::Element, Self::Element>;

    /// Remove the most recently push element, if any.
    #[must_use]
    fn pop(&mut self) -> Option<Self::Element>;

    /// Query which element would next be popped.
    #[must_use]
    fn peek(&self) -> Option<&Self::Element>;
}
