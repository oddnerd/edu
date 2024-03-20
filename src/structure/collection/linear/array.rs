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
    Linear<'a>
    + std::ops::Index<usize, Output = &'a Self::Element>
    + std::ops::IndexMut<usize, Output = &'a mut Self::Element>
    + std::ops::DerefMut<Target = [Self::Element]>
{
    // Obtain an immutable reference to the element at `index`, bounds checked.
    fn at(&self, index: usize) -> Option<&Self::Element> {
        if index < self.count() {
            Some(&self[index])
        } else {
            None
        }
    }

    // Obtain a mutable reference to the element at `index`, bounds checked.
    fn at_mut(&self, index: usize) -> Option<&mut Self::Element> {
        if index < self.count() {
            Some(&mut self[index])
        } else {
            None
        }
    }

    /// Obtain an immutable slice to the elements.
    fn as_slice(&self) -> &[Self::Element] {
        self.deref()
    }

    /// Obtain a mutable slice to the elements.
    fn as_mut_slice(&mut self) -> &mut [Self::Element] {
        self.deref_mut()
    }
}
