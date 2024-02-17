//! Operators for [`Fixed`].

use super::Fixed;

impl<T, const N: usize> std::ops::Index<usize> for Fixed<T, N> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        debug_assert!(index < N);
        // SAFETY:
        // * index is within bounds => the pointer is within bounds
        // * `add` in alignments of T => properly aligned pointer
        // * underlying array exists => points to initalized T
        unsafe { &*self.data.as_ptr().add(index) }
    }
}

impl<T, const N: usize> std::ops::IndexMut<usize> for Fixed<T, N> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        debug_assert!(index < N);
        // SAFETY:
        // * index is within bounds => the pointer is within bounds
        // * `add` in alignments of T => properly aligned pointer
        // * underlying array exists => points to initalized T
        unsafe { &mut *self.data.as_mut_ptr().add(index) }
    }
}

impl<T, const N: usize> std::ops::Deref for Fixed<T, N> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // SAFETY:
        // * `data` is aligned => pointer is aligned
        // * `data` is initalized => every element is initalized
        // * `data` is one object => slice is over one allocated object
        unsafe { std::slice::from_raw_parts(self.data.as_ptr(), N) }
    }
}

impl<T, const N: usize> std::ops::DerefMut for Fixed<T, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY:
        // * `data` is aligned => pointer is aligned
        // * `data` is initalized => every element is initalized
        // * `data` is one object => slice is over one allocated object
        unsafe { std::slice::from_raw_parts_mut(self.data.as_mut_ptr(), N) }
    }
}
