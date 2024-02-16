//! Linear collections are ones which logically arrange the elements sequentially.

use super::Collection;

/// A [`Collection`] whose elements are logically arranged sequentially.
pub trait Linear: Collection {}
