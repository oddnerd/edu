//! Implementations of [`Collection`].

pub mod linear;
pub mod graph;

pub use linear::Linear;
pub use graph::Graph;

/// A data structure which stores multiple elements of a single type.
pub trait Collection {
    /// The type of the elements.
    type Element;

    /// Query the number of elements.
    #[must_use]
    fn count(&self) -> usize;

    /// Query if no elements are contained.
    #[must_use]
    fn is_empty(&self) -> bool {
        self.count() == 0
    }
}
