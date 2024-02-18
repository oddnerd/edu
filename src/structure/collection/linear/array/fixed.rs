//! Implementation of [`Fixed`].

pub mod iter;
pub mod ops;
/// Fixed size (statically stack allocated) [`Array`].
pub struct Fixed<T, const N: usize> {
    data: [T; N],
}

impl<T, const N: usize> Fixed<T, N> {
    /// Create a [`Fixed`] from some a primitive array.
    pub fn new(array: [T; N]) -> Self {
        Self { data: array }
    }
}

impl<'a, T: 'a, const N: usize> super::super::Collection<'a> for Fixed<T, N> {
    type Element = T;

    fn count() -> usize {
        N
    }
}

impl<'a, T: 'a, const N: usize> super::Linear<'a> for Fixed<T, N> {
    fn iter(&self) -> impl std::iter::Iterator<Item = &'a Self::Element> {
        iter::Iter::new(self)
    }

    fn iter_mut(&mut self) -> impl std::iter::Iterator<Item = &'a mut Self::Element> {
        iter::IterMut::new(self)
    }
}

impl<T, const N: usize> std::borrow::Borrow<[T]> for Fixed<T, N> {
    fn borrow(&self) -> &[T] {
        self
    }
}

impl<T, const N: usize> std::borrow::BorrowMut<[T]> for Fixed<T, N> {
    fn borrow_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<T, const N: usize> std::convert::AsRef<[T]> for Fixed<T, N> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, const N: usize> std::convert::AsMut<[T]> for Fixed<T, N> {
    fn as_mut(&mut self) -> &mut [T] {
        self
    }
}

impl<'a, T: 'a, const N: usize> super::Array<'a> for Fixed<T, N> {}
