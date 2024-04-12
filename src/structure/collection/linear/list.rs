//! Implementations of [`List`].

use super::Linear;

/// [`Linear`] [`Collection`] which can insert or remove elements.
pub trait List<'a>:
    Linear<'a>
    + IntoIterator<Item = Self::Element>
    + Iterator<Item = Self::Element>
    + DoubleEndedIterator<Item = Self::Element>
    + ExactSizeIterator
    + std::iter::FusedIterator
    + FromIterator<Self::Element>
{
    /// Insert an `element` at `index`.
    ///
    /// The elements `[..index]` remain unmodified whereas elements `[index..]`
    /// are shifted to the right such that they become `[index + 1..]`, and the
    /// element at `index` is the `element` being inserted.
    fn insert(
        &mut self,
        index: usize,
        element: Self::Element,
    ) -> Result<&mut Self::Element, Self::Element>;

    /// Remove the element at `index`.
    ///
    /// The elements at `[..index]` remain unmodified, the element at `index`
    /// is dropped, and the elements `[index + 1..]` are shifted to the left
    /// such that they become `[index..]`.
    fn remove(&mut self, index: usize) -> Option<Self::Element>;

    /// Remove the element at the front, the first element.
    fn front(&mut self) -> Option<Self::Element> {
        self.next()
    }

    /// Remove the element at the back, the last element.
    fn back(&mut self) -> Option<Self::Element> {
        self.next_back()
    }

    /// Insert an element such that it becomes the first.
    fn prepend(&mut self, element: Self::Element) -> Result<&mut Self::Element, Self::Element> {
        self.insert(0, element)
    }

    /// Insert an element such that is becomes the last.
    fn append(&mut self, element: Self::Element) -> Result<&mut Self::Element, Self::Element> {
        self.insert(self.len(), element)
    }

    /// Drop all elements.
    fn clear(&mut self) {
        for _ in 0..self.count() {
            let _element = self.remove(0).expect("element to remove");
        }
    }
}
