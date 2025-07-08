//! Implementations of [`List`].

use super::Collection;
use super::Linear;

pub mod singly;
pub use singly::Singly;

pub mod doubly;
pub use doubly::Doubly;
