//! Implementations of [`Graph`].

pub mod tree;

pub use tree::Tree;

use super::Collection;

/// Complex associations ([`Edge`]) between elements ([`Node`]).
pub trait Graph : Collection {
    /// Type used to connect via [`Edge`].
    type Node: Node;

    /// Type used to represent connection between [`Node`].
    type Edge<'a>: Edge<'a> where Self::Element: 'a;
}

/// An instantiated element with a [`Graph`].
pub trait Node {}

/// A connection/link/association between [`Node`] within a [`Graph`].
pub trait Edge<'a> {}
