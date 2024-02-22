//! Implementation of [`Dope`].


/// [Dope Vector](https://en.wikipedia.org/wiki/Dope_vector) implementation,
/// (i.e., [Rust's slice](https://doc.rust-lang.org/std/primitive.slice.html)).
struct Dope<T, N> {
    data: *mut T,
}
