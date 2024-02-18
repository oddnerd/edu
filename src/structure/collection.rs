//! [Collections](https://en.wikipedia.org/wiki/Collection_(abstract_data_type))
//! are data structures which store multiple elements of a sinlge type.

pub mod linear;

/// Multiple instances of a single type grouped together.
pub trait Collection<'a> {
    /// The type of the elements stored within.
    type Element: 'a;

    /// Query the number of elements stored within.
    fn count() -> usize;
}
