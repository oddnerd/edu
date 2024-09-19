//! Implementations of [`Graph`].

pub mod tree;

pub use tree::Tree;

use super::Collection;

/// Complex associations ([`Edge`]) between elements ([`Node`]).
pub trait Graph : Collection {}
