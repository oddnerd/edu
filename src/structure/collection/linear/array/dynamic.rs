//! Implementation of [`Dynamic`].

use super::Array;
use super::Collection;
use super::Linear;

/// An [`Array`] which can store a runtime defined number of elements.
///
/// A contigious memory buffer with sequentially laid out elements at alignment
/// divisions. The buffer is lazily heap-allocated to store some number of
/// elements, referred to as the capacity. Elements are sequentially
/// initialized within the buffer as they are inserted reducing the capacity.
/// Once the capacity has been exhausted, the buffer is reallocated to contain
/// previously initialized elements followed by new uninitialized capacity.
///
/// See also: [Wikipedia](https://en.wikipedia.org/wiki/Dynamic_array).
pub struct Dynamic<T> {
    /// Underlying buffer storing initialized _and_ uninitialized elements.
    data: std::ptr::NonNull<std::mem::MaybeUninit<T>>,

    /// The number of elements which are currently initialized.
    initialized: usize,

    /// The number of elements which are allocated but currently uninitialized.
    allocated: usize,
}

impl<T> Dynamic<T> {
    /// Construct an empty instance.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let instance: Dynamic<()> = Dynamic::new();
    ///
    /// assert_eq!(instance.count(), 0);
    /// assert_eq!(instance.capacity(), 0);
    /// ```
    pub fn new() -> Self {
        Self {
            data: std::ptr::NonNull::dangling(),
            initialized: 0,
            allocated: 0,
        }
    }

    /// Construct an instance with an allocated buffer for `count` elements.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let instance = Dynamic<()>::with_capacity(4).expect("bad allocation");
    ///
    /// assert_eq!(instance.count(), 0);
    /// assert!(instance.capacity() >= 4);
    /// ```
    pub fn with_capacity(count: usize) -> Option<Self> {
        let mut instance = Self::new();
        if instance.reserve(count) {
            Some(instance)
        } else {
            None
        }
    }

    /// Query how many elements could be inserted without allocation.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance: Dynamic<i32> = Dynamic::with_capacity(2).unwrap();
    ///
    /// let old_capacity = instance.capacity();
    /// assert!(old_capacity >= 2);
    ///
    /// instance.append(1);
    /// instance.append(2);
    /// assert_eq!(instance.capacity(), old_capacity - 2);
    /// ```
    pub fn capacity(&self) -> usize {
        self.allocated
    }

    /// Attempt to allocate space for `capacity` additional elements.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance: Dynamic<()> = Dynamic::new();
    /// assert_eq!(instance.capacity(), 0);
    ///
    /// instance.reserve(16);
    /// assert!(instance.capacity() >= 16);
    /// ```
    pub fn reserve(&mut self, capacity: usize) -> bool {
        if std::mem::size_of::<T>() == 0 {
            self.allocated = usize::MAX;
            return true;
        }

        if self.allocated > capacity || capacity == 0 {
            return true;
        }

        // growth factor of two (2) so capacity is doubled each reallocation.
        let size = match self.initialized.checked_add(capacity) {
            Some(size) => size,
            None => return false,
        }
        .next_power_of_two();

        let layout = match std::alloc::Layout::array::<T>(size) {
            Ok(layout) => layout,
            Err(_) => return false,
        };

        let old_size = self.initialized + self.allocated;

        let ptr = if old_size == 0 {
            // SAFETY: non-zero-size type => `layout` has non-zero size.
            unsafe { std::alloc::alloc(layout) }
        } else {
            let new_size = layout.size();
            let layout = match std::alloc::Layout::array::<T>(old_size) {
                Ok(layout) => layout,
                Err(_) => return false,
            };

            // SAFETY: non-zero-size type => `layout` has non-zero size.
            unsafe { std::alloc::realloc(self.data.cast::<u8>().as_ptr(), layout, new_size) }
        };

        // SAFETY: [`MaybeUninit<T>`] has the same layout at `T`.
        let ptr = ptr.cast::<std::mem::MaybeUninit<T>>();

        self.data = match std::ptr::NonNull::new(ptr) {
            Some(ptr) => ptr,
            None => return false,
        };

        self.allocated = size - self.initialized;

        true
    }

    /// Attempt to shrink the capacity to exactly `capacity`, or none/zero.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let instance = Dynamic<()>::with_capacity(16);
    /// assert!(instance.capacity() >= 16);
    ///
    /// instance.shrink(Some(8));
    /// assert_eq!(instance.capacity(), 8);
    ///
    /// instance.shrink(None);
    /// assert_eq!(instance.capacity(), 0);
    /// ```
    pub fn shrink(&mut self, capacity: Option<usize>) -> bool {
        if capacity.is_some_and(|capacity| capacity >= self.allocated) {
            return false;
        }

        let capacity = capacity.unwrap_or(0);

        if std::mem::size_of::<T>() == 0 {
            self.allocated = capacity;
            return true;
        }

        let old_size = self.initialized + self.allocated;
        let layout = match std::alloc::Layout::array::<T>(old_size) {
            Ok(layout) => layout,
            Err(_) => return false,
        };

        let size = self.initialized + capacity;
        let new_size = match std::alloc::Layout::array::<T>(capacity) {
            Ok(layout) => layout,
            Err(_) => return false,
        }
        .size();

        // SAFETY: non-zero-size type => `layout` has non-zero size.
        let ptr = unsafe { std::alloc::realloc(self.data.cast::<u8>().as_ptr(), layout, new_size) };

        // SAFETY: [`MaybeUninit<T>`] has the same layout at `T`.
        let ptr = ptr.cast::<std::mem::MaybeUninit<T>>();

        self.data = match std::ptr::NonNull::new(ptr) {
            Some(ptr) => ptr,
            None => return false,
        };

        self.allocated = size - self.initialized;

        true
    }

    /// Drop all elements.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    /// use rust::structure::collection::Collection;
    ///
    /// let mut instance = Dynamic::from([0, 1, 2, 3].as_slice());
    /// assert_eq!(instance.count(), 4);
    ///
    /// instance.clear();
    ///
    /// assert_eq!(instance.count(), 0);
    /// assert!(instance.capacity() >= 4);
    /// ```
    pub fn clear(&mut self) {
        if std::mem::size_of::<T>() == 0 {
            self.initialized = 0;
            self.allocated = usize::MAX;
            return;
        }

        while self.initialized > 0 {
            let ptr = self.data.as_ptr();

            // SAFETY: `ptr` remains within the allocated object.
            let ptr = unsafe { ptr.add(self.initialized - 1) };

            // SAFETY: `ptr` is pointing to the last initialized element.
            unsafe { (*ptr).assume_init_drop() };

            self.allocated += self.initialized;
            self.initialized = 0;
        }
    }

    /// Attempt to add an `element` to the end, allocating if necessary.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic<i32>::new();
    ///
    /// instance.append(1);
    /// instance.append(2);
    ///
    /// assert_eq!(instance.count(), 2);
    /// assert_eq!(instance.first(), 1);
    /// assert_eq!(instance.last(), 2);
    /// ```
    pub fn append(&mut self, element: T) -> bool {
        if self.allocated == 0 && !self.reserve(1) {
            return false;
        }

        if std::mem::size_of::<T>() == 0 {
            self.initialized += 1;
            self.allocated -= 1;
            return true;
        }

        unsafe {
            // SAFETY: the buffer has been allocated.
            let ptr = self.data.as_ptr();

            // SAFETY: this points to the first uninitialized element.
            let ptr = ptr.add(self.initialized);

            // SAFETY:
            // * `ptr` is non-null.
            // * `ptr` is aligned.
            // * the [`MaybeUninit<T>`] is initialized even if the `T` isn't.
            (*ptr).write(element);
        };

        self.initialized += 1;

        true
    }

    /// Attempt to insert `element` at `index`, allocating if necessary.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::from([0, 1, 2, 3].as_slice());
    ///
    /// instance.insert(7, 1);
    ///
    /// assert_eq!(instance[0], 0);
    /// assert_eq!(instance[1], 7);
    /// assert_eq!(instance[2], 1);
    /// assert_eq!(instance[3], 2);
    /// assert_eq!(instance[4], 3);
    /// ```
    pub fn insert(&mut self, element: T, index: usize) -> bool {
        if index >= self.initialized {
            return false;
        }

        if self.allocated == 0 && !self.reserve(1) {
            return false;
        }

        if std::mem::size_of::<T>() == 0 {
            self.initialized += 1;
            self.allocated -= 1;
            return true;
        }

        // shift initialized elements `[index..]` one position to the right.
        unsafe {
            // SAFETY: aligned within the allocated object.
            let from = self.data.as_ptr().add(index);

            // SAFETY: capacity was confirmed so this is also within the object.
            let to = from.add(1);

            // SAFETY: owned memory and no aliasing despite overlapping.
            std::ptr::copy(from, to, self.initialized - index);

            // SAFETY: update internal state to reflect shift.
            self.initialized += 1;
            self.allocated -= 1;
        }

        unsafe {
            // SAFETY: aligned within the allocated object.
            let ptr = self.data.as_ptr().add(index);

            // SAFETY:
            // * `ptr` points to the uninitialized element created by shifting.
            // * `ptr` is mutably owned.
            (*ptr).write(element);
        };

        true
    }

    /// Drop the element at `index`, shifting following elements.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::from([0, 1, 2, 3].as_slice());
    /// assert_eq!(instance.count(), 4);
    ///
    /// instance.remove(2);
    ///
    /// assert_eq!(instance.count(), 3);
    /// assert_eq!(instance[0], 0);
    /// assert_eq!(instance[0], 1);
    /// assert_eq!(instance[0], 3);
    /// ```
    pub fn remove(&mut self, index: usize) -> Option<T> {
        if index >= self.initialized {
            return None;
        }

        if std::mem::size_of::<T>() == 0 {
            self.initialized -= 1;
            self.allocated = self.allocated.saturating_add(1);

            // SAFETY:
            // * pointer is aligned.
            // * pointer is non-null.
            // * zero-sized type makes this special-case [`ptr::read`] okay.
            return Some(unsafe { std::ptr::NonNull::<T>::dangling().as_ptr().read() });
        }

        let element = unsafe {
            // SAFETY: stays aligned within the allocated object.
            let element = self.data.as_ptr().add(index);

            // SAFETY: `T` has the same layout as [`MaybeUninit<T>`].
            let element = element.cast::<T>();

            // SAFETY: the element is initialized.
            element.read()
        };

        // shift initialized elements `[index + 1..]` one position to the left.
        unsafe {
            // SAFETY: element at `index` was removed hence it is uninitialized.
            let to = self.data.as_ptr().add(index);

            // SAFETY: whereas this is the first initialized element after.
            let from = to.add(1);

            // SAFETY: owned memory and no aliasing despite overlapping.
            std::ptr::copy(from, to, self.initialized - index);

            // SAFETY: update internal state to reflect shift.
            self.initialized -= 1;
            self.allocated += 1;
        }

        Some(element)
    }
}

impl<T> std::ops::Drop for Dynamic<T> {
    fn drop(&mut self) {
        if self.initialized + self.allocated == 0 || std::mem::size_of::<T>() == 0 {
            return;
        }

        for index in 0..self.initialized {
            // SAFETY: stays aligned within the allocated object.
            let ptr = unsafe { self.data.as_ptr().add(index) };

            // SAFETY: points to an initialized instance.
            unsafe { ptr.as_mut().unwrap_unchecked().assume_init_drop() };
        }

        let layout = std::alloc::Layout::array::<T>(self.initialized + self.allocated).unwrap();

        // SAFETY:
        // * `self.data` was allocated with the global allocator.
        // * `layout` was used for the allocation.
        unsafe { std::alloc::dealloc(self.data.as_ptr().cast::<u8>(), layout) };
    }
}

impl<'a, T: 'a + Clone> std::convert::From<&'a [T]> for Dynamic<T> {
    fn from(slice: &'a [T]) -> Self {
        let mut instance = Self::with_capacity(slice.len()).unwrap_or_default();

        if std::mem::size_of::<T>() == 0 {
            instance.initialized = slice.len();
            instance.allocated = usize::MAX - instance.initialized;
        } else {
            for element in slice {
                instance.append(element.clone());
            }
        }

        instance
    }
}

impl<'a, T: 'a> super::Collection<'a> for Dynamic<T> {
    type Element = T;

    fn count(&self) -> usize {
        self.initialized
    }
}

/// By-value [`Iterator`] over a [`Dynamic`].
pub struct IntoIter<T> {
    /// ownership of the values.
    data: std::ptr::NonNull<std::mem::MaybeUninit<T>>,

    /// The layout `data` was allocated with.
    layout: std::alloc::Layout,

    /// elements within this range have yet to be yielded.
    next: std::ops::Range<usize>,
}

impl<T> std::ops::Drop for IntoIter<T> {
    fn drop(&mut self) {
        for index in self.next.clone() {
            // SAFETY: stays aligned within the allocated object.
            let element = unsafe { self.data.as_ptr().add(index) };

            // SAFETY:
            // * owns underlying memory buffer => valid for reads and writes.
            // * within `self.next` => pointing to initialized value.
            unsafe { (*element).assume_init_drop() };
        }

        // SAFETY:
        // * `self.data` was allocated with the global allocator.
        // * `self.layout` was used for the allocation.
        unsafe { std::alloc::dealloc(self.data.as_ptr().cast::<u8>(), self.layout) };
    }
}

impl<T> std::iter::Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next.start != self.next.end {
            let element = {
                // SAFETY: `T` has same layout as [`MaybeUninit<T>`].
                let ptr = self.data.as_ptr().cast::<T>();

                // SAFETY: stays aligned within the allocated object.
                let ptr = unsafe { ptr.add(self.next.start) };

                // SAFETY: the element is initialized.
                unsafe { ptr.read() }
            };

            self.next.start += 1;

            Some(element)
        } else {
            None
        }
    }
}

impl<T> std::iter::IntoIterator for Dynamic<T> {
    type Item = T;

    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            data: self.data,
            layout: std::alloc::Layout::array::<T>(self.initialized + self.allocated).unwrap(),
            next: 0..self.initialized,
        }
    }
}

impl<'a, T: 'a> super::Linear<'a> for Dynamic<T> {
    fn iter(&self) -> impl std::iter::Iterator<Item = &'a Self::Element> {
        // # SAFETY:
        // * `self.data` points to one contigious allocated object.
        // * `self.len` consecutive initialized and aligned instances.
        unsafe { super::iter::Iter::new(self.data.cast::<T>(), self.initialized) }
    }

    fn iter_mut(&mut self) -> impl std::iter::Iterator<Item = &'a mut Self::Element> {
        // # SAFETY:
        // * `self.data` points to one contigious allocated object.
        // * `self.len` consecutive initialized and aligned instances.
        unsafe { super::iter::IterMut::new(self.data.cast::<T>(), self.initialized) }
    }

    fn first(&self) -> Option<&Self::Element> {
        if self.initialized > 0 {
            // SAFETY:
            // * `T` has same layout as [`MaybeUninit<T>`].
            // * points to an initialized value.
            Some(unsafe { self.data.cast::<T>().as_ref() })
        } else {
            None
        }
    }

    fn last(&self) -> Option<&Self::Element> {
        if self.initialized > 0 {
            // SAFETY: `T` has same layout as [`MaybeUninit<T>`].
            let element = self.data.cast::<T>().as_ptr();

            // SAFETY: stays within the allocated object.
            let element = unsafe { element.add(self.initialized - 1) };

            // SAFETY: the element is initialized.
            unsafe { element.as_ref() }
        } else {
            None
        }
    }
}

impl<T> std::ops::Index<usize> for Dynamic<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < self.initialized);
        // SAFETY:
        // * `data` is [`NonNull`] => pointer will be non-null.
        // * index is within bounds => `add` stays within the allocated object.
        // * `add` => pointer is aligned.
        // * `T` has the same layout as [`MaybeUninit<T>`] => safe cast.
        // * underlying object is initialized => points to initialized `T`.
        // * lifetime bound to self => valid lifetime to return.
        unsafe { &*self.data.as_ptr().cast::<T>().add(index) }
    }
}

impl<T> std::ops::IndexMut<usize> for Dynamic<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert!(index < self.initialized);
        // SAFETY:
        // * `data` is [`NonNull`] => pointer will be non-null.
        // * index is within bounds => `add` stays within bounds.
        // * `add` => pointer is aligned.
        // * `T` has the same layout as [`MaybeUninit<T>`] => safe cast.
        // * underlying object is initialized => points to initialized `T`.
        // * lifetime bound to self => valid lifetime to return.
        unsafe { &mut *self.data.as_ptr().cast::<T>().add(index) }
    }
}

impl<T> std::ops::Deref for Dynamic<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        // SAFETY:
        // * `data` is aligned => pointer is aligned.
        // * `T` has the same layout as [`MaybeUninit<T>`] => safe cast.
        // * `self.initialized` => every element is initialized.
        // * `data` is one object => slice is over one allocated object.
        unsafe { std::slice::from_raw_parts(self.data.as_ptr().cast::<T>(), self.initialized) }
    }
}

impl<T> std::ops::DerefMut for Dynamic<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // SAFETY:
        // * `data` is aligned => pointer is aligned.
        // * `T` has the same layout as [`MaybeUninit<T>`] => safe cast.
        // * `self.initialized` => every element is initialized.
        // * `data` is one object => slice is over one allocated object.
        unsafe { std::slice::from_raw_parts_mut(self.data.as_ptr().cast::<T>(), self.initialized) }
    }
}

impl<'a, T: 'a> Array<'a> for Dynamic<T> {}

impl<T: PartialEq> PartialEq for Dynamic<T> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T: Eq> std::cmp::Eq for Dynamic<T> {}

impl<T: std::fmt::Debug> std::fmt::Debug for Dynamic<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T> std::default::Default for Dynamic<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> Clone for Dynamic<T> {
    fn clone(&self) -> Self {
        let mut clone = Self::with_capacity(self.count()).unwrap_or_default();

        for element in self.iter() {
            clone.append(element.clone());
        }

        clone
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new() {
        let instance = Dynamic::<()>::new();

        assert_eq!(instance.initialized, 0);
        assert_eq!(instance.allocated, 0);
    }

    #[test]
    fn from_slice() {
        // sized type.
        {
            let array = [0, 1, 2, 3];
            let instance = Dynamic::from(array.as_slice());
            assert!(instance.iter().eq(array.iter()));
        }

        // zero-size type.
        {
            let array = [(), (), (), ()];
            let instance = Dynamic::from(array.as_slice());
            assert!(instance.iter().eq(array.iter()));
        }
    }

    #[test]
    fn with_capacity() {
        // sized type.
        {
            let instance = Dynamic::<i32>::with_capacity(4).unwrap();

            assert_eq!(instance.initialized, 0);
            assert!(instance.allocated >= 4);
        }

        // zero-size type.
        {
            let instance = Dynamic::<()>::with_capacity(4).unwrap();

            assert_eq!(instance.initialized, 0);
            assert!(instance.allocated >= 4);
        }
    }

    #[test]
    fn count() {
        let instance = Dynamic::<()>::new();

        assert_eq!(instance.count(), 0);
    }

    #[test]
    fn capacity() {
        let instance = Dynamic::<()>::new();

        assert_eq!(instance.capacity(), 0);
    }

    #[test]
    fn reserve() {
        // sized type.
        {
            let mut instance = Dynamic::<i32>::new();
            assert_eq!(instance.allocated, 0);

            // initial allocation.
            instance.reserve(8);
            assert!(instance.allocated >= 8);

            // reallocation.
            instance.reserve(256);
            assert!(instance.allocated >= 256);

            // does not shrink.
            instance.reserve(0);
            assert!(instance.allocated > 0);
        }

        // zero-size type.
        {
            let mut instance = Dynamic::<()>::new();
            assert_eq!(instance.allocated, 0);

            // initial allocation.
            instance.reserve(8);
            assert!(instance.allocated >= 8);

            // reallocation.
            instance.reserve(256);
            assert!(instance.allocated >= 256);

            // does not shrink.
            instance.reserve(0);
            assert!(instance.allocated > 0);
        }
    }

    #[test]
    fn shrink() {
        // sized type.
        {
            let mut instance = Dynamic::<i32>::with_capacity(16).unwrap();
            instance.append(0);
            assert!(instance.allocated >= 15);

            // reduces capacity.
            instance.shrink(Some(8));
            assert_eq!(instance.allocated, 8);

            // eliminates capacity.
            instance.shrink(None);
            assert_eq!(instance.allocated, 0);

            // doesn't remove initialized elements.
            assert_eq!(instance.initialized, 1);
            assert_eq!(instance[0], 0);
        }

        // zero-size type.
        {
            let mut instance = Dynamic::<()>::with_capacity(16).unwrap();
            instance.append(());
            assert!(instance.allocated >= 15);

            // reduces capacity.
            instance.shrink(Some(8));
            assert_eq!(instance.allocated, 8);

            // eliminates capacity.
            instance.shrink(None);
            assert_eq!(instance.allocated, 0);

            // doesn't remove initialized elements.
            assert_eq!(instance.initialized, 1);
            assert_eq!(instance[0], ());
        }
    }

    #[test]
    fn append() {
        // sized type.
        {
            let mut instance = Dynamic::<i32>::new();
            assert_eq!(instance.initialized, 0);

            // empty instance.
            instance.append(1);
            assert_eq!(instance.initialized, 1);

            // instance with one element.
            instance.append(2);
            assert_eq!(instance.initialized, 2);

            // instance with more than one element.
            instance.append(3);
            assert_eq!(instance.initialized, 3);

            // element goes to end, otherwise order preserved
            assert_eq!(instance[0], 1);
            assert_eq!(instance[1], 2);
            assert_eq!(instance[2], 3);
        }

        // zero-size types.
        {
            let mut instance = Dynamic::<()>::new();
            assert_eq!(instance.initialized, 0);

            // empty instance.
            instance.append(());
            assert_eq!(instance.initialized, 1);

            // instance with one element.
            instance.append(());
            assert_eq!(instance.initialized, 2);

            // instance with more than one element.
            instance.append(());
            assert_eq!(instance.initialized, 3);

            // element goes to end, otherwise order preserved
            assert_eq!(instance[0], ());
            assert_eq!(instance[1], ());
            assert_eq!(instance[2], ());
        }
    }

    #[test]
    fn insert() {
        // sized type.
        {
            // one element.
            let mut instance = Dynamic::from([1].as_slice());
            instance.insert(0, 0);
            assert_eq!(instance[0], 0);
            assert_eq!(instance[1], 1);

            // front element.
            let mut instance = Dynamic::from([1, 2].as_slice());
            instance.insert(0, 0);
            assert_eq!(instance[0], 0);
            assert_eq!(instance[1], 1);
            assert_eq!(instance[2], 2);

            // end element.
            let mut instance = Dynamic::from([0, 2].as_slice());
            instance.insert(1, 1);
            assert_eq!(instance[0], 0);
            assert_eq!(instance[1], 1);
            assert_eq!(instance[2], 2);

            // middle element.
            let mut instance = Dynamic::from([0, 1, 3, 4, 5].as_slice());
            instance.insert(2, 2);
            assert_eq!(instance[0], 0);
            assert_eq!(instance[1], 1);
            assert_eq!(instance[2], 2);
            assert_eq!(instance[3], 3);
            assert_eq!(instance[4], 4);
            assert_eq!(instance[5], 5);
        }

        // zero-size type.
        {
            // one element.
            let mut instance = Dynamic::from([()].as_slice());
            instance.insert((), 0);
            assert_eq!(instance[0], ());
            assert_eq!(instance[1], ());

            // front element.
            let mut instance = Dynamic::from([(), ()].as_slice());
            instance.insert((), 0);
            assert_eq!(instance[0], ());
            assert_eq!(instance[1], ());
            assert_eq!(instance[2], ());

            // end element.
            let mut instance = Dynamic::from([(), ()].as_slice());
            instance.insert((), 1);
            assert_eq!(instance[0], ());
            assert_eq!(instance[1], ());
            assert_eq!(instance[2], ());

            // middle element.
            let mut instance = Dynamic::from([(), (), (), (), ()].as_slice());
            instance.insert((), 2);
            assert_eq!(instance[0], ());
            assert_eq!(instance[1], ());
            assert_eq!(instance[2], ());
            assert_eq!(instance[3], ());
            assert_eq!(instance[4], ());
            assert_eq!(instance[5], ());
        }
    }

    #[test]
    fn remove() {
        // sized type.
        {
            // one element.
            let mut instance = Dynamic::from([0].as_slice());
            instance.remove(0);
            assert_eq!(instance.initialized, 0);

            // front element.
            let mut instance = Dynamic::from([0, 1].as_slice());
            instance.remove(0);
            assert_eq!(instance.initialized, 1);
            assert_eq!(instance[0], 1);

            // last element.
            let mut instance = Dynamic::from([0, 1].as_slice());
            instance.remove(1);
            assert_eq!(instance.initialized, 1);
            assert_eq!(instance[0], 0);

            // middle element.
            let mut instance = Dynamic::from([0, 1, 2, 3, 4].as_slice());
            instance.remove(2);
            assert_eq!(instance.initialized, 4);
            assert_eq!(instance[0], 0);
            assert_eq!(instance[1], 1);
            assert_eq!(instance[2], 3);
            assert_eq!(instance[3], 4);
        }

        // zero-size type.
        {
            // one element.
            let mut instance = Dynamic::from([()].as_slice());
            instance.remove(0);
            assert_eq!(instance.initialized, 0);

            // front element.
            let mut instance = Dynamic::from([(), ()].as_slice());
            instance.remove(0);
            assert_eq!(instance.initialized, 1);
            assert_eq!(instance[0], ());

            // last element.
            let mut instance = Dynamic::from([(), ()].as_slice());
            instance.remove(1);
            assert_eq!(instance.initialized, 1);
            assert_eq!(instance[0], ());

            // middle element.
            let mut instance = Dynamic::from([(), (), (), (), ()].as_slice());
            instance.remove(2);
            assert_eq!(instance.initialized, 4);
            assert_eq!(instance[0], ());
            assert_eq!(instance[1], ());
            assert_eq!(instance[2], ());
            assert_eq!(instance[3], ());
        }
    }

    #[test]
    fn clear() {
        // sized type.
        {
            let mut instance = Dynamic::from([0, 1, 2, 3, 4].as_slice());
            let old_capacity = instance.allocated;

            instance.clear();

            assert_eq!(instance.allocated, old_capacity.saturating_add(5));
            assert_eq!(instance.initialized, 0);
        }

        // zero-size type.
        {
            let mut instance = Dynamic::from([(), (), (), (), ()].as_slice());
            let old_capacity = instance.allocated;

            instance.clear();

            assert!(instance.allocated >= old_capacity.saturating_add(5));
            assert_eq!(instance.initialized, 0);
        }
    }

    #[test]
    fn into_iter() {
        // sized type.
        {
            let array = [0, 1, 2, 3];
            let instance = Dynamic::from(array.as_slice());

            assert!(instance.into_iter().eq(array.into_iter()));
        }

        // zero-size type.
        {
            let array = [(), (), (), ()];
            let instance = Dynamic::from(array.as_slice());

            assert!(instance.into_iter().eq(array.into_iter()));
        }
    }

    #[test]
    fn iter() {
        // sized type.
        {
            let array = [0, 1, 2, 3];
            let instance = Dynamic::from(array.as_slice());

            assert!(instance.iter().eq(array.iter()));
        }

        // zero-size type.
        {
            let array = [(), (), (), ()];
            let instance = Dynamic::from(array.as_slice());

            assert!(instance.iter().eq(array.iter()));
        }
    }

    #[test]
    fn iter_mut() {
        // sized type.
        {
            let mut array = [0, 1, 2, 3];
            let mut instance = Dynamic::from(array.as_slice());

            assert!(instance.iter_mut().eq(array.iter_mut()));
        }

        // zero-size type.
        {
            let mut array = [0, 1, 2, 3];
            let mut instance = Dynamic::from(array.as_slice());

            assert!(instance.iter_mut().eq(array.iter_mut()));
        }
    }

    #[test]
    fn first() {
        // sized type.
        {
            let instance = Dynamic::from([0, 1, 2, 3].as_slice());
            assert_eq!(*instance.first().unwrap(), instance[0]);
        }

        // zero-sized type.
        {
            let instance = Dynamic::from([(), (), (), ()].as_slice());
            assert_eq!(*instance.first().unwrap(), instance[0]);
        }
    }

    #[test]
    fn last() {
        // sized type.
        {
            let instance = Dynamic::from([0, 1, 2, 3].as_slice());
            assert_eq!(*instance.last().unwrap(), instance[3]);
        }

        // zero-size type.
        {
            let instance = Dynamic::from([(), (), (), ()].as_slice());
            assert_eq!(*instance.last().unwrap(), instance[3]);
        }
    }

    #[test]
    fn index() {
        // sized type.
        {
            let instance = Dynamic::from([0, 1, 2, 3].as_slice());

            assert_eq!(instance[0], 0);
            assert_eq!(instance[1], 1);
            assert_eq!(instance[2], 2);
            assert_eq!(instance[3], 3);
        }

        // zero-size type.
        {
            let instance = Dynamic::from([0, 1, 2, 3].as_slice());

            assert_eq!(instance[0], 0);
            assert_eq!(instance[1], 1);
            assert_eq!(instance[2], 2);
            assert_eq!(instance[3], 3);
        }
    }

    #[test]
    fn index_mut() {
        // sized type.
        {
            let mut instance = Dynamic::from([0, 1, 2, 3].as_slice());

            instance[0] = 4;
            instance[1] = 5;
            instance[2] = 6;
            instance[3] = 7;

            assert_eq!(instance[0], 4);
            assert_eq!(instance[1], 5);
            assert_eq!(instance[2], 6);
            assert_eq!(instance[3], 7);
        }

        // zero-size type.
        {
            let mut instance = Dynamic::from([0, 1, 2, 3].as_slice());

            instance[0] = 4;
            instance[1] = 5;
            instance[2] = 6;
            instance[3] = 7;

            assert_eq!(instance[0], 4);
            assert_eq!(instance[1], 5);
            assert_eq!(instance[2], 6);
            assert_eq!(instance[3], 7);
        }
    }

    #[test]
    fn deref() {
        // sized type.
        {
            let array = [0, 1, 2, 3];
            let instance = Dynamic::from(array.as_slice());

            use std::ops::Deref;
            assert_eq!(instance.deref(), array.as_slice());
        }

        // zero-size type.
        {
            let array = [(), (), (), ()];
            let instance = Dynamic::from(array.as_slice());

            use std::ops::Deref;
            assert_eq!(instance.deref(), array.as_slice());
        }
    }

    #[test]
    fn deref_mut() {
        // sized type.
        {
            let array = [0, 1, 2, 3];
            let mut instance = Dynamic::from(array.as_slice());

            use std::ops::DerefMut;
            assert_eq!(instance.deref_mut(), array.as_slice());
        }

        // zero-size type.
        {
            let array = [(), (), (), ()];
            let mut instance = Dynamic::from(array.as_slice());

            use std::ops::DerefMut;
            assert_eq!(instance.deref_mut(), array.as_slice());
        }
    }

    #[test]
    fn eq() {
        // sized type.
        {
            let instance = Dynamic::from([0, 1, 2, 3].as_slice());
            let other = Dynamic::from([0, 1, 2, 3].as_slice());

            assert_eq!(instance, other);
        }

        // zero-size type.
        {
            let instance = Dynamic::from([(), (), (), ()].as_slice());
            let other = Dynamic::from([(), (), (), ()].as_slice());

            assert_eq!(instance, other);
        }
    }

    #[test]
    fn ne() {
        // sized type.
        {
            let instance = Dynamic::from([0, 1, 2, 3].as_slice());
            let other = Dynamic::from([4, 5, 6, 7].as_slice());

            assert_ne!(instance, other);
        }

        // zero-size type.
        {
            let instance = Dynamic::from([(), ()].as_slice());
            let other = Dynamic::from([(), (), (), ()].as_slice());

            assert_ne!(instance, other);
        }
    }

    #[test]
    fn default() {
        let instance: Dynamic<()> = Default::default();

        assert_eq!(instance.initialized, 0);
        assert_eq!(instance.allocated, 0);
    }

    #[test]
    fn clone() {
        // sized type
        {
            let instance = Dynamic::from([0, 1, 2, 3].as_slice());
            let clone = instance.clone();

            assert_ne!(instance.data, clone.data);
            assert_eq!(instance, clone);
        }

        // zero-size type
        {
            let instance = Dynamic::from([(), (), (), ()].as_slice());
            let clone = instance.clone();

            assert_eq!(instance, clone);
        }
    }
}
