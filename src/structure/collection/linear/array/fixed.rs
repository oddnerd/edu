//! Implementation of a static (fixed size) [`Array`].

/// [Dope Vector](https://en.wikipedia.org/wiki/Dope_vector) interpretation of
/// an array using memory layout to define the structure.
pub struct Fixed<T, const N: usize> {
    dope: *mut T,
}

impl<'a, T: 'a, const N: usize> super::super::Collection<'a> for Fixed<T, N> {
    type Element = T;

    fn count() -> usize {
        N
    }
}
