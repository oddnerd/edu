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
    /// assert_eq!(instance.count(), 0);
    /// assert_eq!(instance.capacity(), 0);
    /// ```
    pub fn new() -> Self {
        Self {
            data: std::ptr::NonNull::dangling(),
            initialized: 0,
            allocated: 0,
        }
    }

    /// Construct an instance with an allocated buffer for `count` elements.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let instance: Dynamic<()> = Dynamic::with_capacity(4);
    /// assert_eq!(instance.count(), 0);
    /// assert_eq!(instance.capacity(), 4);
    /// ```
    pub fn with_capacity(count: usize) -> Option<Self> {
        let mut instance = Self::new();

        // SAFETY: the underlying buffer has _not_ yet been allocated.
        if unsafe { instance.alloc(count) } {
            instance.allocated = count;
            Some(instance)
        } else {
            None
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

    /// Pre-allocate memory for `count` additional elements.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance: Dynamic<()> = Dynamic::new();
    /// assert_eq!(instance.capacity(), 0);
    /// instance.reserve(8);
    /// assert_eq!(instance.capacity(), 8);
    /// ```
    pub fn reserve(&mut self, count: usize) -> bool {
        if self.initialized + self.allocated == 0 {
            // SAFETY: the underlying buffer has _not_ yet been allocated.
            if unsafe { self.alloc(count) } {
                self.allocated = count;
                return true;
            }
        } else {
            if count < self.allocated {
                // enough space is already reserved.
                return true;
            } else {
                // SAFETY: the underlying buffer has been previously allocated.
                if unsafe { self.realloc(self.initialized + count) } {
                    self.allocated = count;
                    return true;
                }
            }
        }

        false
    }

    /// Allocate a buffer to hold exactly `count` elements.
    ///
    /// Returns `true` if the allocation is successful, false otherwise.
    ///
    /// # Safety
    /// * the underlying buffer must not yet be allocated.
    /// * this method does not update member variables.
    unsafe fn alloc(&mut self, count: usize) -> bool {
        if let Ok(layout) = std::alloc::Layout::array::<T>(count) {
            if layout.size() > 0 {
                // SAFETY: `layout` has non-zero size.
                let ptr = unsafe { std::alloc::alloc(layout) };

                // SAFETY: `MaybeUninit<T>` has same layout as `T`.
                let ptr = ptr.cast::<std::mem::MaybeUninit<T>>();

                if let Some(ptr) = std::ptr::NonNull::new(ptr) {
                    self.data = ptr;
                    return true;
                }
            } else if std::mem::size_of::<T>() == 0 {
                return true;
            }
        }

        false
    }

    /// Resize the underlying buffer to hold exactly `count` elements.
    ///
    /// Returns `true` if the allocation is successful, false otherwise.
    ///
    /// # Safety
    /// * the underlying buffer must already be allocated, _not_ dangling.
    /// * this method does not update member variables.
    unsafe fn realloc(&mut self, count: usize) -> bool {
        let old = std::alloc::Layout::array::<T>(self.initialized + self.allocated);
        let new = std::alloc::Layout::array::<T>(count);

        match (old, new) {
            (Ok(old), Ok(new)) => {
                if new.size() > 0 {
                    // SAFETY: `layout` has non-zero size.
                    let ptr = unsafe {
                        let ptr = self.data.as_ptr() as *mut u8;
                        std::alloc::realloc(ptr, old, new.size())
                    };

                    // SAFETY: `MaybeUninit<T>` has same layout as `T`.
                    let ptr = ptr.cast::<std::mem::MaybeUninit<T>>();

                    if let Some(ptr) = std::ptr::NonNull::new(ptr) {
                        self.data = ptr;
                        return true;
                    }
                } else if std::mem::size_of::<T>() == 0 {
                    return true;
                }
            }
            (_, _) => {}
        }

        false
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
        let instance: Dynamic<()> = Dynamic::with_capacity(4).unwrap();

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

    #[test]
    fn reserve() {
        let mut instance: Dynamic<()> = Dynamic::new();

        assert_eq!(instance.allocated, 0);

        instance.reserve(8);

        assert_eq!(instance.allocated, 8);

        instance.reserve(16);

        assert_eq!(instance.allocated, 16);
    }
}
