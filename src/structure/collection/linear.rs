//! Implementations of [`Linear`].

pub mod array;
pub mod list;

pub use array::Array;
pub use list::List;

use super::Collection;

/// A [`Collection`] with sequential ordering.
///
/// # Layout
///
/// This trait does not enforce the layout of memory, it instead denotes a
/// logical layout of elements. The primary characteristic of this trait
/// is that such [`Collection`] have exactly one (bidirectional) method of
/// iteration ([`Self::iter`]/[`Self::iter_mut`]) that allows access to all
/// contained elements.
///
/// The elements are arranged such that starting from the [`Self::first`]
/// element, there exists exactly one element after it, and exactly one element
/// after that element, iterating to the element after through every contained
/// element. Likewise starting from the  [`Self::last`] element, there exists
/// exactly one element before it, and exactly one element before that element,
/// iterating to the element before through every contained element.
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
/// The [`Self::first`] and [`Self::last`] element are the ends of a line made
/// up of elements connected end-to-end. This means the elements inherently
/// have some specific ordering which can be leveraged to uniquely index each
/// element. Denoted above within parenthesis is the index scheme used by
/// implementors of this trait. If we arbitrarily denote the [`Self::first`]
/// element to have index of value zero ([zero-based indexing][zbi]), then each
/// subsequent element can have index one greater than the element before it,
/// hence the index increments by one for each element.
///
/// The methods [`Self::at`] and [`Self::at_mut`] provide access to the element
/// at some given index, but will do bounds checking which means they are safe
/// to input indexes which are past the last element likely at the cost of some
///  performance. In contrast, [`std::ops::Index`] and [`std::ops::IndexMut`]
/// do _not_ bounds check instead causing undefined behaviour if an out of
/// bounds index is provided, but this allows you to have external logic
/// associating indexes to elements which prevents erroneous inputs.
///
/// [zbi]: https://en.wikipedia.org/wiki/Zero-based_numbering
pub trait Linear<'a>: Collection<'a> + std::ops::IndexMut<usize, Output = Self::Element> {
    /// Iterate over the elements by immutable reference.
    fn iter(
        &self,
    ) -> impl DoubleEndedIterator<Item = &'a Self::Element> + ExactSizeIterator + std::iter::FusedIterator;

    /// Iterate over the elements by mutable reference.
    fn iter_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = &'a mut Self::Element>
           + ExactSizeIterator
           + std::iter::FusedIterator;

    /// Obtain an immutable reference to the element at `index`, bounds checked.
    fn at(&self, index: usize) -> Option<&Self::Element> {
        if index < self.count() {
            Some(&self[index])
        } else {
            None
        }
    }

    /// Obtain a mutable reference to the element at `index`, bounds checked.
    fn at_mut(&mut self, index: usize) -> Option<&mut Self::Element> {
        if index < self.count() {
            Some(&mut self[index])
        } else {
            None
        }
    }

    /// Query the element considered to be at the front, the first element.
    fn first(&self) -> Option<&Self::Element> {
        self.at(0)
    }

    /// Query the element considered to be at the back, the last element.
    fn last(&self) -> Option<&Self::Element> {
        self.at(self.count() - 1)
    }

    /// Obtain a reference to the element at the front, the first element.
    fn first_mut(&mut self) -> Option<&mut Self::Element> {
        self.at_mut(0)
    }

    /// Obtain a reference to the element at the back, the last element.
    fn last_mut(&mut self) -> Option<&mut Self::Element> {
        self.at_mut(self.count() - 1)
    }
}
