//! Implementations of [`Collection`].
//!
//! Included within are:
//!
//! * [`Linear`] relationships where elements have sequential ordering.

pub mod linear;

pub use linear::Linear;

/// A data structure which stores multiple elements of a single type.
pub trait Collection<'a> {
    /// The type of the elements.
    type Element: 'a;

    /// Query the number of elements.
    fn count(&self) -> usize;

    /// Query if no elements are contained.
    fn is_empty(&self) -> bool {
        self.count() == 0
    }
}
