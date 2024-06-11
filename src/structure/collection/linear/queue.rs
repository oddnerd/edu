//! Implementation of [`Queue`].

use super::Collection;
use super::Linear;

/// A [`Linear`] [`Collection`] with first-in-first-out (FIFO) semantics.
///
/// See also: [Wikipedia](https://en.wikipedia.org/wiki/Queue_(abstract_data_type)).
pub trait Queue: Collection + Linear {
    /// Add a new element at the end of the queue.
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
