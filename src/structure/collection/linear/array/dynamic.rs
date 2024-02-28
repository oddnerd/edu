//! Implementation of a [dynamically sized array](https://en.wikipedia.org/wiki/Dynamic_array).

use super::Array;
use super::Collection;
use super::Linear;

/// An [`Array`] which can store a runtime defined number of elements.
///
/// A contigious memory buffer with sequentially laid out elements at alignment
/// divisions. The buffer is lazily heap-allocated to store some number of
/// elements, referred to as the capacity. Elements are sequentially
/// initialized within the buffer as they are appended reducing the capacity.
/// Once the capacity has been exhausted, the buffer is reallocated to contain
/// previously initialized elements followed by new uninitialized capacity.
pub struct Dynamic<T> {
    /// Underlying buffer storing initialized _and_ uninitialized elements.
    data: std::ptr::NonNull<std::mem::MaybeUninit<T>>,

    /// The number of elements which are currently initialized.
    initialized: usize,

    /// The number of elements which are allocated but currently uninitialized.
    allocated: usize,
}

impl<T> Dynamic<T> {
    /// Construct an empty instance.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let instance: Dynamic<()> = Dynamic::new();
    /// todo!("assert!(instance.is_empty())");
    /// assert_eq!(instance.count(), 0);
    /// todo!("assert_eq!(instance.capacity(), 0)");
    /// ```
    pub fn new() -> Self {
        Self {
            data: std::ptr::NonNull::dangling(),
            initialized: 0,
            allocated: 0,
        }
    }

    /// Query how many elements could be inserted without allocation.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// todo!("make the following example work");
    /// let mut instance: Dynamic<i32> = Dynamic::with_capacity(2);
    /// assert_eq!(instance.capacity(), 2);
    /// instance.append(1);
    /// instance.append(2);
    /// assert_eq!(instance.capacity(), 0);
    /// ```
    pub fn capacity(&self) -> usize {
        self.allocated
    }
}

impl<'a, T: 'a> super::Collection<'a> for Dynamic<T> {
    type Element = T;

    fn count(&self) -> usize {
        self.initialized
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new() {
        let instance: Dynamic<()> = Dynamic::new();

        assert_eq!(instance.initialized, 0);
        assert_eq!(instance.allocated, 0);
    }

    #[test]
    fn with_capacity() {
        let instance: Dynamic<()> = Dynamic::with_capacity(4);

        assert_eq!(instance.initialized, 0);
        assert_eq!(instance.allocated, 4);
    }

    #[test]
    fn count() {
        let instance: Dynamic<()> = Dynamic::new();

        assert_eq!(instance.count(), 0);
    }

    #[test]
    fn capacity() {
        let instance: Dynamic<()> = Dynamic::new();

        assert_eq!(instance.capacity(), 0);
    }
}
