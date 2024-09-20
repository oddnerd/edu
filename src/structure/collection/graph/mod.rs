//! Implementations of [`Graph`].

pub mod tree;

pub use tree::Tree;

use super::Collection;

pub trait Graph : Collection {}

pub trait Node {}

pub trait Edge<'a> {}
