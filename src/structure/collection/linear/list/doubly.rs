//! Implementation of [`Doubly`].

use core::ptr::NonNull;

use super::Collection;
use super::Linear;
use super::List;

/// Independently allocated elements connected via two links.
///
/// Each element exists within separate allocated object, referred to as a
/// node. Each node contains a pointer to the previous node alongside a pointer
/// to the subsequent node whereas [`Self`] maintains a pointer to the first
/// _and_ last node as visualized below:
///
/// ```text
///         +-------+ -> +---------+ -> +---------+ -> ... -> +------+
/// Self -> | first |    | element |    | element |           | last | <- Self
///         +-------+ <- +---------+ <- +---------+ <- ... <- +------+
/// ```
///
/// See also: [Wikipedia](https://en.wikipedia.org/wiki/Linked_list)
pub struct Doubly<T> {
    /// The node considered to be the first/front, if any are contained.
    head: Option<NonNull<Node<T>>>,

    /// The node considered to be the last/back, if any are contained.
    tail: Option<NonNull<Node<T>>>,
}

/// An independently allocated element contained within some [`Doubly`].
struct Node<T> {
    /// Ownership of the underlying element.
    element: T,

    /// The node before self, if any.
    predecessor: Option<NonNull<Node<T>>>,

    /// The node after self, if any.
    successor: Option<NonNull<Node<T>>>,
}

impl<T> Drop for Doubly<T> {
    fn drop(&mut self) {
        todo!()
    }
}

impl<T> Default for Doubly<T> {
    fn default() -> Self {
        todo!();
    }
}

impl<T: Clone> Clone for Doubly<T> {
    fn clone(&self) -> Self {
        todo!()
    }
}

impl<T: PartialEq> PartialEq for Doubly<T> {
    fn eq(&self, other: &Self) -> bool {
        todo!()
    }
}

impl<T: Eq> Eq for Doubly<T> {}

impl<T: core::fmt::Debug> core::fmt::Debug for Doubly<T> {
    fn fmt(&self, output: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        todo!()
    }
}

impl<T> core::ops::Index<usize> for Doubly<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        todo!()
    }
}

impl<T> core::ops::IndexMut<usize> for Doubly<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        todo!()
    }
}

impl<T> Iterator for Doubly<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        todo!()
    }
}

impl<T> DoubleEndedIterator for Doubly<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<T> ExactSizeIterator for Doubly<T> {}

impl<T> core::iter::FusedIterator for Doubly<T> {}

impl<T> Extend<T> for Doubly<T> {
    fn extend<Iter: IntoIterator<Item = T>>(&mut self, elements: Iter) {
        todo!()
    }
}

impl<T> FromIterator<T> for Doubly<T> {
    fn from_iter<Iter: IntoIterator<Item = T>>(elements: Iter) -> Self {
        todo!()
    }
}

impl<T> Collection for Doubly<T> {
    type Element = T;

    fn count(&self) -> usize {
        todo!()
    }
}

impl<T> Linear for Doubly<T> {
    fn iter(
        &self,
    ) -> impl DoubleEndedIterator<Item = &Self::Element> + ExactSizeIterator + core::iter::FusedIterator
    {
        Iter {
            lifetime: core::marker::PhantomData,
        }
    }

    fn iter_mut(
        &mut self,
    ) -> impl DoubleEndedIterator<Item = &mut Self::Element>
           + ExactSizeIterator
           + core::iter::FusedIterator {
        IterMut {
            lifetime: core::marker::PhantomData,
        }
    }
}

impl<T> List for Doubly<T> {
    fn insert(
        &mut self,
        index: usize,
        element: Self::Element,
    ) -> Result<&mut Self::Element, Self::Element> {
        todo!()
    }

    fn remove(&mut self, index: usize) -> Option<Self::Element> {
        todo!()
    }

    fn drain(
        &mut self,
        range: impl core::ops::RangeBounds<usize>,
    ) -> impl DoubleEndedIterator<Item = Self::Element> + ExactSizeIterator {
        Drain {
            lifetime: core::marker::PhantomData,
        }
    }

    fn withdraw(
        &mut self,
        predicate: impl FnMut(&Self::Element) -> bool,
    ) -> impl DoubleEndedIterator<Item = Self::Element> {
        Withdraw {
            lifetime: core::marker::PhantomData,
        }
    }
}

struct Iter<'a, T> {
    lifetime: core::marker::PhantomData<&'a T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        todo!()
    }
}

impl<T> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {}

impl<T> core::iter::FusedIterator for Iter<'_, T> {}

struct IterMut<'a, T> {
    lifetime: core::marker::PhantomData<&'a mut T>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        todo!()
    }
}

impl<T> DoubleEndedIterator for IterMut<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<T> ExactSizeIterator for IterMut<'_, T> {}

impl<T> core::iter::FusedIterator for IterMut<'_, T> {}

struct Drain<'a, T> {
    lifetime: core::marker::PhantomData<&'a mut T>,
}

impl<T> Drop for Drain<'_, T> {
    fn drop(&mut self) {
        todo!()
    }
}

impl<T> Iterator for Drain<'_, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        todo!()
    }
}

impl<T> DoubleEndedIterator for Drain<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<T> ExactSizeIterator for Drain<'_, T> {}

impl<T> core::iter::FusedIterator for Drain<'_, T> {}

struct Withdraw<'a, T> {
    lifetime: core::marker::PhantomData<&'a mut T>,
}

impl<T> Drop for Withdraw<'_, T> {
    fn drop(&mut self) {
        todo!()
    }
}

impl<T> Iterator for Withdraw<'_, T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        todo!()
    }
}

impl<T> DoubleEndedIterator for Withdraw<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<T> ExactSizeIterator for Withdraw<'_, T> {}

impl<T> core::iter::FusedIterator for Withdraw<'_, T> {}

#[cfg(test)]
#[allow(
    clippy::undocumented_unsafe_blocks,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::assertions_on_result_states,
    clippy::indexing_slicing
)]
mod test {
    use super::*;

    mod default {
        use super::*;

        #[test]
        fn has_no_elements() {
            let actual = Doubly::<()>::default();

            assert!(actual.head.is_none());
            assert!(actual.tail.is_none());
        }
    }
}
