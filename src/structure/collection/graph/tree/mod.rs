//! Implementations of [`Tree`].

use super::Graph;

/// A [`Graph`] where the only relationships are hierarchical.
///
/// TODO: explain recursive nature.
pub trait Tree : Graph<Node = Self> {
    /// Immutably obtain the top-level [`Node`].
    fn root(&self) -> &Self::Node;

    /// Mutably obtain the top-level [`Node`].
    fn root_mut(&mut self) -> &mut Self::Node;

    /// Query the length of the longest chain of [`Node`].
    fn height(&self) -> usize;
}
