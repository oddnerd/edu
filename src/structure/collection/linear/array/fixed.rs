//! Implementation of a static (fixed size) [`Array`].

/// [Dope Vector](https://en.wikipedia.org/wiki/Dope_vector) interpretation of
/// an array using memory layout to define the structure.
pub struct Fixed<T> {
    dope: *mut T,
}
