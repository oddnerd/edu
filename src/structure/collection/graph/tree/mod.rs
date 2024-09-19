//! Implementations of [`Tree`].

pub mod binary;

pub use binary::Binary;

use super::Graph;
use super::Collection;

/// A [`Graph`] where the only relationships are hierarchical.
pub trait Tree : Graph {}
