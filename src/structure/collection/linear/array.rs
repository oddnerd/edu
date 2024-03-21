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
use super::LinearMut;

/// A [`Linear`] [`Collection`] which occupies contigious memory.
///
/// Implementations of this trait store elements within one allocated object
/// at appropriate alignment boundaries separated only by padding, if any.
///
/// See also: [Wikipedia](https://en.wikipedia.org/wiki/Array_(data_type)).
pub trait Array<'a>: Linear<'a> {
    /// Obtain an immutable pointer to the underlying contigious memory buffer.
    ///
    /// # Safety
    /// * The object this pointer is derived from must outlive said pointer.
    /// * The pointer must not be invalidated by modifying the object.
    unsafe fn as_ptr(&self) -> *const Self::Element;

    /// Obtain a mutable pointer to the underlying contigious memory buffer.
    ///
    /// # Safety
    /// * The object this pointer is derived from must outlive said pointer.
    /// * The pointer must not be invalidated by modifying the object.
    unsafe fn as_mut_ptr(&mut self) -> *mut Self::Element;

    /// Obtain an immutable slice to the elements.
    fn as_slice(&self) -> &[Self::Element] {
        unsafe { std::slice::from_raw_parts(self.as_ptr(), self.count()) }
    }

    /// Obtain a mutable slice to the elements.
    fn as_mut_slice(&mut self) -> &mut [Self::Element] {
        unsafe { std::slice::from_raw_parts_mut(self.as_mut_ptr(), self.count()) }
    }
}
