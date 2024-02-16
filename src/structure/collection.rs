//! [Collections](https://en.wikipedia.org/wiki/Collection_(abstract_data_type)) are data structures which store elements of a shared type together.

/// A collection is a structure to group elements of a single type.
pub trait Collection {
    /// The type of the elements stored within.
    type Element;
}
