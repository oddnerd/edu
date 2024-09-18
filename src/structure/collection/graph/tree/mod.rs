//! Implementations of [`Tree`].

use super::Graph;

/// A [`Graph`] where the only relationships are hierarchical.
pub trait Tree : Graph {
    /// Immutably obtain the top-level [`Node`].
    fn root(&self) -> &Self::Node;

    /// Mutably obtain the top-level [`Node`].
    fn root_mut(&mut self) -> &mut Self::Node;
}
