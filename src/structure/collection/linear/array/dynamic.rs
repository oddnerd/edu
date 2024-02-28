//! Implementation of a [dynamically sized array](https://en.wikipedia.org/wiki/Dynamic_array).

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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new() {
        let instance: Dynamic<()> = Dynamic::new();

        assert_eq!(instance.initialized, 0);
        assert_eq!(instance.allocated, 0);
    }
}
