//! Implementation of [`Dope`].

use super::Array;
use super::Collection;
use super::Linear;

/// [Dope Vector](https://en.wikipedia.org/wiki/Dope_vector) implementation
/// (i.e., [Rust's slice](https://doc.rust-lang.org/std/primitive.slice.html))
/// uses a pointer-length pair alongside type information to map an array upon
/// an object buffer in memory.
pub struct Dope<'a, T: 'a> {
    data: *mut T,
    len: usize,
    lifetime: std::marker::PhantomData<&'a T>,
}

impl<'a, T: 'a> Collection<'a> for Dope<'a, T> {
    type Element = T;

    fn count(&self) -> usize {
        self.len
    }
}
