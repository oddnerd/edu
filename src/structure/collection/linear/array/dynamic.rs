//! Implementation of a [dynamically sized array](https://en.wikipedia.org/wiki/Dynamic_array).

pub struct Dynamic<T> {
    data: std::ptr::NonNull<T>,
    initialized: usize,
    allocated: usize,
}
