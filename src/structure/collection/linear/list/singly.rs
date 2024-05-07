//! Implementation of [`Singly`].

use super::List;

use std::alloc;

/// Independently allocated elements connected via a single link.
///
/// Each element exists with a 'node', each of which are a separate allocated
/// object. These nodes are logically arranged in [`Self::Linear`] fashion
/// where each element links to the element after it and nothing else.
///
/// See also: [Wikipedia](https://en.wikipedia.org/wiki/Linked_list).
pub struct Singly<T> {
    /// The contained element for this node.
    element: T,

    /// The next element, if there is one.
    next: Option<Box<Singly<T>>>,
}
