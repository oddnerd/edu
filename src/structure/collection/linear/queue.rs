//! Implementation of [`Queue`].

use super::Collection;
use super::Linear;

/// A [`Linear`] [`Collection`] with first-in-first-out (FIFO) semantics.
///
/// Elements are physically ordered by the relative insertion order and
/// accessed in that order such that elements can be [`Self::pop`]ped removing
/// an element at a time from least to most recently inserted by
/// [`Self::push`]ing.
///
/// This can be visualized as a horizontal line of elements as visualize below
/// where elements are pushed onto the left end popped via the right. The order
/// is `[A, B, C]` such that A is the least recently pushed element, and C is
/// the most recently pushed. Therefore popping will removed A followed by B
/// and then C.
///
/// ```
///            +---+     +---+     +---+
/// pushed --> | C | --> | B | --> | A | --> popped
///            +---+     +---+     +---+
/// ```
///
/// See also: [Wikipedia](https://en.wikipedia.org/wiki/Stack_(abstract_data_type)).
pub trait Queue: Collection + Linear {
    /// Insert an element.
    ///
    /// # Errors
    /// Yields the `element` when it cannot be inserted.
    fn push(&mut self, element: Self::Element) -> Result<&mut Self::Element, Self::Element>;

    /// Remove an element.
    #[must_use]
    fn pop(&mut self) -> Option<Self::Element>;

    /// The element which would be returned is [`Self::pop`] was called.
    #[must_use]
    fn peek(&self) -> Option<&Self::Element>;
}
