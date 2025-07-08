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
/// This can be visualized as vertical 'stack' of elements as visualized below
/// where only the uncovered top can be accessed. The order is `[C, B, A]` such
/// that C is the least recently pushed element, and A is the most recently
/// pushed. Therefore popping will first remove A followed by B and then C.
///
/// ```
/// +---+
/// | A |
/// +---+
/// | B |
/// +---+
/// | C |
/// +---+
/// ```
///
/// See also: [Wikipedia](https://en.wikipedia.org/wiki/Stack_(abstract_data_type)).
pub trait Stack: Collection + Linear {
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
