//! Implementations of [`Collection`].

pub mod linear;

pub use linear::Linear;

/// A data structure which stores multiple instances of a single type.
pub trait Collection {
    /// The type that is instantiated.
    type Element;

    /// How many instances are contained.
    #[must_use]
    fn cardinality(&self) -> usize;

    /// Query if any instances are contained.
    #[must_use]
    fn is_empty(&self) -> bool {
        self.cardinality() == 0
    }
}
