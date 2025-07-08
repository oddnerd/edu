//! Implementations of [`Array`].

mod iter;
use iter::Iter;
use iter::IterMut;

pub mod dope;
pub use dope::Dope;

pub mod fixed;
pub use fixed::Fixed;

pub mod dynamic;
pub use dynamic::Dynamic;

use super::Collection;
use super::Linear;

/// A [`Linear`] [`Collection`] which occupies contigious memory.
///
/// Implementations of this trait store elements within one allocated object
/// at appropriate alignment boundaries separated only by padding, if any.
///
/// See also: [Wikipedia](https://en.wikipedia.org/wiki/Array_(data_type)).
pub trait Array: Linear {
    /// Obtain an immutable pointer to the underlying contigious memory buffer.
    fn as_ptr(&self) -> *const Self::Element;

    /// Obtain a mutable pointer to the underlying contigious memory buffer.
    fn as_mut_ptr(&mut self) -> *mut Self::Element;

    /// Obtain an inclusive start and exclusive end pointer range.
    fn as_ptr_range(&self) -> core::ops::Range<*const T>;

    /// Obtain an inclusive start and exclusive end pointer range.
    fn as_mut_ptr_range(&mut self) -> core::ops::Range<*mut T>;
}
