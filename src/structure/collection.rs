//! [Collections](https://en.wikipedia.org/wiki/Collection_(abstract_data_type)) are data structures which store elements of a shared type together.

pub mod linear;

/// A collection is a structure to group elements of a single type.
pub trait Collection<'a> {
    /// The type of the elements stored within.
    type Element: 'a;

    /// Query the number of elements stored within.
    fn count() -> usize;
}
