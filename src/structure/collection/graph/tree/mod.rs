//! Implementations of [`Tree`].

pub mod binary;

pub use binary::Binary;

use super::Graph;
use super::Collection;

pub trait Tree : Graph {}
