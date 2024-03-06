//! Implementations of [`Array`].

pub mod iter;
pub use iter::Iter;
pub use iter::IterMut;

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
pub trait Array<'a>:
    Linear<'a> + std::ops::IndexMut<usize> + std::ops::DerefMut<Target = [Self::Element]>
{
}
