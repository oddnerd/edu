//! Implementations of [`Tree`].

use super::Graph;

/// A [`Graph`] where the only relationships are hierarchical.
pub trait Tree<T> : Graph<T> {}
