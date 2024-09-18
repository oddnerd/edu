//! Implementations of [`Tree`].

use super::Graph;

/// A [`Graph`] where the only relationships are hierarchical.
///
/// TODO: explain recursive nature.
pub trait Tree : Graph<Node = Self> {
    /// Immutably obtain the [`Node`] whose parent is `self`.
    fn children<'a>(&'a self) -> impl Iterator<Item = &'a Self::Node> where Self::Node: 'a;

    /// Mutably obtain the [`Node`] whose parent is `self`.
    fn children_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut Self::Node> where Self::Node: 'a;

    /// Immutably obtain the [`Node`] for which `self` is a child.
    fn parent(&self) -> &Self::Node;

    /// Mutably obtain the [`Node`] for which `self` is a child.
    fn parent_mut(&mut self) -> &mut Self::Node;

    /// Immutably obtain the top-level [`Node`] of the entire [`Tree`].
    fn root(&self) -> &Self::Node;

    /// Mutably obtain the top-level [`Node`] of the entire [`Tree`].
    fn root_mut(&mut self) -> &mut Self::Node;

    /// Query the longest length of chain of [`Node`] from `self` to a leaf.
    fn height(&self) -> usize;

    /// Query the length of the chain of [`Node`] between the root and `self`.
    fn level(&self) -> usize;

    /// Query the maximum number of children a [`Node`] can have.
    fn degree(&self) -> usize;

    /// Query the number of siblings this [`Node`] has.
    fn width(&self) -> usize;
}
