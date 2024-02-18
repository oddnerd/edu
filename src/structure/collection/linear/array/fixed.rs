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

    fn count(&self) -> usize {
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

impl<T: Default, const N: usize> std::default::Default for Fixed<T, N> {
    fn default() -> Self {
        // SAFETY: the MaybeUninit it initalized even if the T isn't.
        let mut uninitalized: [std::mem::MaybeUninit<T>; N] =
            unsafe { std::mem::MaybeUninit::uninit().assume_init() };

        for element in uninitalized.iter_mut() {
            element.write(Default::default());
        }

        // SAFETY:
        // * MaybeUninit<T> has same size as T => arrays have same size
        // * MaybeUninit<T> has same alignment as T => elements aligned
        let initalized = unsafe { uninitalized.as_mut_ptr().cast::<[T; N]>().read() };

        Self::new(initalized)
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::super::Collection;
    use super::*;

    #[test]
    fn default_zero_elements() {
        let array: Fixed<i32, 0> = Default::default();
        assert_eq!(array.count(), 0);
    }

    #[test]
    fn default_one_elements() {
        let array: Fixed<i32, 1> = Default::default();
        assert_eq!(array.count(), 1);
        assert_eq!(array[0], Default::default());
    }

    #[test]
    fn default_multiple_elements() {
        let array: Fixed<i32, 256> = Default::default();
        assert_eq!(array.count(), 256);
        for element in array {
            assert_eq!(element, Default::default());
        }
    }
}
