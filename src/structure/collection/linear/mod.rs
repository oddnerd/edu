//! Implementations of [`Linear`].

pub mod array;
pub mod list;
pub mod queue;
pub mod stack;

pub use array::Array;
pub use list::List;
pub use queue::Queue;
pub use stack::Stack;

use super::Collection;

/// A [`Collection`] with sequential ordering.
///
/// # Layout
///
/// This trait does not enforce the layout of memory, it instead denotes a
/// logical layout of elements. The primary characteristic of this trait
/// is that such [collections](`Collection`) have exactly one (bidirectional)
/// method of iteration ([`iter`](`Self::iter`)/[`iter_mut`](`Self::iter_mut`))
/// that allows access to all contained elements.
///
/// The elements are arranged such that starting from the
/// [`first`](`Self::first`) element, there exists exactly one element after
/// it, and exactly one element after that element, iterating to the element
/// after through every contained element. Likewise starting from the
/// [`last`](`Self::last`) element, there exists exactly one element before it,
/// and exactly one element before that element, iterating to the element
/// before through every contained element.
///
/// # Indexing
///
/// The layout described above implies elements are stored one-dimensionally
/// such that the only relationship between them is they occur 'before' or
/// 'after' one another as visualized below:
///
/// ```text
/// +-----------+-------------+-------------+-------------+-----+------+
/// | first (0) | element (1) | element (2) | element (3) | ... | last |
/// +-----------+-------------+-------------+-------------+-----+------+
/// ```
///
/// The [`first`](`Self::first`) and [`last`](`Self::last`) element are the
/// ends of a line made up of elements connected end-to-end. This means the
/// elements inherently have some specific ordering which can be leveraged to
/// uniquely index each element. Denoted above within parenthesis is the index
/// scheme used by implementors of this trait. If we arbitrarily denote the
/// [`first`](`Self::first`) element to have index of value zero
/// ([zero-based indexing][zbi]), then each subsequent element can have index
/// one greater than the element before it, hence the index increments by one
/// for each element.
///
/// The methods [`at`](`Self::at`)/[`at_mut`](`Self::at_mut`) provide access to
/// the element at some given index, but will do bounds checking which means
/// they are safe to input indexes which are past the last element likely at
/// the cost of some performance. In contrast, [`index`](`core::ops::Index`)
/// and [`index_mut`](`core::ops::IndexMut`) do _not_ bounds check instead
/// causing undefined behaviour if an out of bounds index is provided, but this
/// allows you to have external logic associating indexes to elements which
/// prevents erroneous inputs.
///
/// [zbi]: https://en.wikipedia.org/wiki/Zero-based_numbering
pub trait Linear: Collection + core::ops::IndexMut<usize, Output = Self::Element> {
    /// Iterate over the elements by immutable reference.
    #[must_use]
    fn iter(
        &self,
    ) -> impl DoubleEndedIterator<Item = &Self::Element> + ExactSizeIterator + core::iter::FusedIterator;

    /// Iterate over the elements by mutable reference.
    #[must_use]
    fn iter_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = &mut Self::Element>
    + ExactSizeIterator
    + core::iter::FusedIterator;

    /// Obtain an immutable reference to them `index` element, bounds checked.
    #[must_use]
    fn at(&self, index: usize) -> Option<&Self::Element> {
        (index < self.count()).then(|| &self[index])
    }

    /// Obtain a mutable reference to the `index` element, bounds checked.
    #[must_use]
    fn at_mut(&mut self, index: usize) -> Option<&mut Self::Element> {
        (index < self.count()).then(|| &mut self[index])
    }

    /// Query the element considered to be at the front, the first element.
    #[must_use]
    fn first(&self) -> Option<&Self::Element> {
        self.at(0)
    }

    /// Query the element considered to be at the back, the last element.
    #[must_use]
    fn last(&self) -> Option<&Self::Element> {
        self.at(self.count().saturating_sub(1))
    }

    /// Obtain a reference to the element at the front, the first element.
    #[must_use]
    fn first_mut(&mut self) -> Option<&mut Self::Element> {
        self.at_mut(0)
    }

    /// Obtain a reference to the element at the back, the last element.
    #[must_use]
    fn last_mut(&mut self) -> Option<&mut Self::Element> {
        self.at_mut(self.count().saturating_sub(1))
    }
}
