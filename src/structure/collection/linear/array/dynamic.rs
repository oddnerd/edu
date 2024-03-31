//! Implementation of [`Dynamic`].

use super::Array;
use super::Collection;
use super::Linear;

/// An [`Array`] which can store a runtime defined number of elements.
///
/// Contigious memory is heap-allocated with alignment and size to store
/// elements of type `T`, referred to as the buffer. Said buffer is either:
/// explicitly allocated via [`Self::with_capacity`] or [`Self::reserve`]; or
/// lazily allocated as elements are added via [`Self::prepend`],
/// [`Self::append`], and [`Self::insert`].
///
/// The elements are arranged such that the beginning of the buffer potentially
/// contains uninitialized memory produced by removing elements via
/// [`Self::front`] or [`Self::remove`] which will be reclaimed when
/// reallocating or adding to the front. Immediately following are all
/// initialized elements ([`Self::count`] many) in the order they were added.
/// The rest of the buffer contains uninitialized memory to hold
/// [`Self::capacity`] elements. The capacity may be reduced via
/// [`Self::shrink`] to reduce the allocation size, or even deallocate an empty
/// buffer.
///
/// See also: [Wikipedia](https://en.wikipedia.org/wiki/Dynamic_array).
pub struct Dynamic<T> {
    /// Underlying buffer storing initialized _and_ uninitialized elements.
    buffer: std::ptr::NonNull<std::mem::MaybeUninit<T>>,

    /// The number of uninitialized elements before the initialized ones.
    pre_capacity: usize,

    /// The number of elements which are initialized.
    initialized: usize,

    /// The number of uninitialized elements after the initialized ones.
    post_capacity: usize,
}

impl<T> Dynamic<T> {
    /// Attempt to allocate enough memory to store exactly `count` elements.
    ///
    /// # Panics
    /// The Rust runtime might panic or otherwise `abort` if allocation fails.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(N) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Collection;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let instance = Dynamic::<i32>::with_capacity(256).expect("successful allocation");
    ///
    /// assert_eq!(Collection::count(&instance), 0);
    /// assert_eq!(instance.capacity(), 256);
    /// ```
    pub fn with_capacity(count: usize) -> Result<Self, ()> {
        let mut instance = Dynamic::<T>::default();
        match instance.resize(count) {
            Ok(_) => Ok(instance),
            Err(_) => Err(()),
        }
    }

    /// Query how many elements could be added without resizing/reallocation.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let instance = Dynamic::<()>::default();
    ///
    /// assert_eq!(instance.capacity(), 0);
    /// ```
    pub fn capacity(&self) -> usize {
        self.post_capacity
    }

    /// Attempt to allocate space for at least `capacity` additional elements.
    ///
    /// # Panics
    /// The Rust runtime might panic or otherwise `abort` if allocation fails.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// const CAPACITY = 256;
    ///
    /// let instance = Dynamic::<()>::default();
    /// instance.reserve(CAPACITY);
    ///
    /// for _ in 0..CAPACITY {
    ///     instance.append(()).expect("no reallocation!");
    /// }
    /// ```
    pub fn reserve(&mut self, capacity: usize) -> Result<&mut Self, ()> {
        // There is already enough capacity.
        if capacity < self.post_capacity {
            return Ok(self);
        }

        let size = match self.initialized.checked_add(capacity) {
            Some(total) => total,
            None => return Err(()),
        };

        // Amortized growth factor of two (2).
        // See: https://en.wikipedia.org/wiki/Dynamic_array#Geometric_expansion_and_amortized_cost
        let size = match size.checked_next_power_of_two() {
            Some(increased_size) => increased_size,
            None => return Err(()),
        };

        self.resize(size)
    }

    /// Attempt to reduce the capacity to exactly `capacity`, or none/zero.
    ///
    /// # Panics
    /// The Rust runtime might panic or otherwise `abort` if allocation fails.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::<()>::with_capacity(256).expect("allocation");
    ///
    /// instance.shrink(Some(128));
    /// assert_eq!(instance.capacity(), 128);
    ///
    /// instance.shrink(None);
    /// assert_eq!(instance.capacity(), 0);
    /// ```
    pub fn shrink(&mut self, capacity: Option<usize>) -> Result<&mut Self, ()> {
        if capacity.is_some_and(|capacity| capacity > self.post_capacity) {
            return Ok(self);
        }

        let capacity = capacity.unwrap_or(0);

        let size = match self.initialized.checked_add(capacity) {
            Some(total) => total,
            None => return Err(()),
        };

        self.resize(size)
    }

    /// Rearrange and/or (re)allocate the buffer to have exactly `capacity`.
    ///
    /// Shifts initialized elements to the beginning of the buffer, allocates
    /// a buffer for `capacity` elements if no allocation, reallocating
    /// otherwise to have exactly `capacity`.
    ///
    /// # Panics
    /// The Rust runtime might panic or otherwise `abort` if allocation fails.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    fn resize(&mut self, capacity: usize) -> Result<&mut Self, ()> {
        // Zero-size types do _NOT_ occupy memory, so no (re/de)allocation.
        if std::mem::size_of::<T>() == 0 {
            self.pre_capacity = 0;
            self.post_capacity = capacity;

            return Ok(self);
        }

        // Shift initialized elements to the start of the buffer.
        if self.pre_capacity > 0 {
            unsafe {
                // SAFETY: `MaybeUninit<T>` has same layout as `T`.
                let destination = self.buffer.as_ptr().cast::<T>();

                // SAFETY: aligned within the allocated object.
                let source = destination.add(self.initialized);

                // SAFETY:
                // * owned memory => source/destination valid for read/writes.
                // * no aliasing restrictions => source and destination can overlap.
                // * underlying buffer is aligned => both pointers are aligned.
                std::ptr::copy(source, destination, self.initialized);
            }

            self.post_capacity += self.pre_capacity;
            self.pre_capacity = 0;

            // Shifting has created enough capacity, no need to reallocate.
            if self.post_capacity == capacity {
                return Ok(self);
            }
        }

        let new_layout = {
            let elements = match self.initialized.checked_add(capacity) {
                Some(total) => total,
                None => return Err(()),
            };

            match std::alloc::Layout::array::<T>(elements) {
                Ok(layout) => layout,
                Err(_) => return Err(()),
            }
        };

        let ptr = {
            // Allocate the buffer.
            if self.initialized + self.post_capacity == 0 {
                if new_layout.size() > 0 {
                    // SAFETY: layout has non-zero size.
                    unsafe { std::alloc::alloc(new_layout).cast::<T>() }
                } else {
                    debug_assert_eq!(capacity, 0);

                    // SAFETY: empty state => pointer will not be read/write.
                    std::ptr::NonNull::<T>::dangling().as_ptr()
                }
            }
            // Modify an existing buffer allocation.
            else {
                let existing_layout = {
                    let elements = match self.initialized.checked_add(self.post_capacity) {
                        Some(total) => total,
                        None => return Err(()),
                    };

                    let layout = match std::alloc::Layout::array::<T>(elements) {
                        Ok(layout) => layout,
                        Err(_) => return Err(()),
                    };

                    layout
                };

                unsafe {
                    // SAFETY: `MaybeUninit<T>` has same layout as `T`.
                    let ptr = self.buffer.as_ptr().cast::<u8>();

                    // Deallocate.
                    if self.initialized == 0 && capacity == 0 {
                        // SAFETY:
                        // * `ptr` was allocated using the corresponding allocator.
                        // * `existing_layout` is currently allocated at `ptr`.
                        // * `new_layout` has non-zero size.
                        // * `Layout` guarantees `new_size.size() <= isize::MAX`.
                        std::alloc::dealloc(ptr, existing_layout);

                        // SAFETY: empty state => pointer will not read/write.
                        std::ptr::NonNull::<T>::dangling().as_ptr()
                    }
                    // Reallocation.
                    else {
                        // SAFETY:
                        // * `ptr` was allocated using the corresponding allocator.
                        // * `existing_layout` is currently allocated at `ptr`.
                        // * `new_layout` has non-zero size.
                        // * `Layout` guarantees `new_size.size() <= isize::MAX`.
                        std::alloc::realloc(ptr, existing_layout, new_layout.size()).cast::<T>()
                    }
                }
            }
        };

        // SAFETY: `MaybeUninit<T>` has the same layout as `T`.
        let ptr = ptr.cast::<std::mem::MaybeUninit<T>>();

        self.buffer = match std::ptr::NonNull::new(ptr) {
            Some(ptr) => ptr,
            None => return Err(()),
        };

        self.post_capacity = capacity;

        Ok(self)
    }
}

impl<T> std::ops::Drop for Dynamic<T> {
    /// Drops the elements that are initialized and deallocates memory.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// instance.next();      // Consumes the element with value `0`.
    /// instance.next_back(); // Consumes the element with value `5`.
    ///
    /// std::mem::drop(instance); // Drops the elements with values `[1, 2, 3, 4]`.
    /// ```
    fn drop(&mut self) {
        for index in 0..self.initialized {
            unsafe {
                let ptr = self.buffer.as_ptr().add(self.pre_capacity);

                // SAFETY: stays aligned within the allocated object.
                let ptr = ptr.add(index);

                // SAFETY:
                // * The `MaybeUninit<T>` is initialized => safe deref.
                // * The `T` is initialized => safe drop.
                (*ptr).assume_init_drop()
            };
        }

        self.post_capacity += self.initialized;
        self.initialized = 0;

        self.post_capacity += self.pre_capacity;
        self.pre_capacity = 0;

        self.resize(0).expect("deallocation cannot fail");
    }
}

impl<'a, T: 'a + Clone> std::convert::TryFrom<&'a [T]> for Dynamic<T> {
    type Error = ();

    /// Construct by cloning elements from an existing slice.
    ///
    /// # Panics
    /// The Rust runtime might panic or otherwise `abort` if allocation fails.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Dynamic::try_from(expected.as_slice()).expect("successful allocation");
    ///
    /// assert!(actual.eq(expected));
    /// ```
    fn try_from(value: &'a [T]) -> Result<Self, Self::Error> {
        let mut instance = Self::with_capacity(value.len())?;

        unsafe {
            // SAFETY: valid for reads up to `value.len()` elements.
            let source = value.as_ptr();

            // SAFETY: `MaybeUninit<T>` has the same layout as `T`.
            let destination = instance.buffer.cast::<T>().as_ptr();

            // SAFETY:
            // * owned memory => destination valid for writes.
            // * no aliasing restrictions => source and destination can overlap.
            // * underlying buffer is aligned => both pointers are aligned.
            std::ptr::copy(source, destination, value.len());
        }

        instance.initialized = value.len();

        Ok(instance)
    }
}

impl<T> std::ops::Index<usize> for Dynamic<T> {
    type Output = T;

    /// Query the initialized element `index` positions from the start.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Dynamic::from_iter(expected.iter().copied());
    ///
    /// for index in 0..expected.len() {
    ///     use std::ops::Index;
    ///     assert_eq!(actual.index(index), expected.index(index));
    /// }
    /// ```
    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < self.initialized);

        unsafe {
            // SAFETY: `buffer` is aligned => `ptr` is aligned.
            let ptr = self.buffer.as_ptr();

            // SAFETY: index within bounds => stays within the allocated object.
            let ptr = ptr.add(self.pre_capacity + index);

            // SAFETY:
            // * the underlying `T` is initialized.
            // * lifetime bound to self => valid lifetime to return.
            (*ptr).assume_init_ref()
        }
    }
}

impl<T> std::ops::IndexMut<usize> for Dynamic<T> {
    /// Obtain a reference to the element `index` positions from the start.
    ///
    /// # Panics
    /// Panics if `index` is out of bounds.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    /// let mut actual = Dynamic::from_iter(expected.iter().copied());
    ///
    /// for index in 0..expected.len() {
    ///     use std::ops::IndexMut;
    ///     assert_eq!(actual.index_mut(index), expected.index_mut(index));
    /// }
    /// ```
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        assert!(index < self.initialized);

        unsafe {
            // SAFETY: `buffer` is aligned => `ptr` is aligned.
            let ptr = self.buffer.as_ptr();

            // SAFETY: index within bounds => stays within the allocated object.
            let ptr = ptr.add(self.pre_capacity + index);

            // SAFETY:
            // * the underlying `T` is initialized.
            // * lifetime bound to self => valid lifetime to return.
            (*ptr).assume_init_mut()
        }
    }
}

impl<T> std::iter::Iterator for Dynamic<T> {
    type Item = T;

    /// Obtain the first initialized element.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]).into_iter();
    ///
    /// assert_eq!(actual.next(), Some(0));
    /// assert_eq!(actual.next(), Some(1));
    /// assert_eq!(actual.next(), Some(2));
    /// assert_eq!(actual.next(), Some(3));
    /// assert_eq!(actual.next(), Some(4));
    /// assert_eq!(actual.next(), Some(5));
    /// assert_eq!(actual.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        if self.initialized > 0 {
            let ptr = self.buffer.as_ptr();

            // SAFETY: stays aligned within the allocated object.
            let ptr = unsafe { ptr.add(self.pre_capacity) };

            self.initialized -= 1;
            self.pre_capacity += 1;

            // SAFETY:
            // * `self.buffer` is non-null => `ptr` is non-null.
            // * The underlying `T` is initialized.
            Some(unsafe { (*ptr).assume_init_read() })
        } else {
            None
        }
    }

    /// Query how many elements have yet to be yielded.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let mut actual = Dynamic::from_iter(expected.clone()).into_iter();
    ///
    /// assert_eq!(actual.size_hint(), expected.into_iter().size_hint());
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.initialized, Some(self.initialized))
    }
}

impl<T> std::iter::FusedIterator for Dynamic<T> {}

impl<T> std::iter::ExactSizeIterator for Dynamic<T> {}

impl<T> std::iter::DoubleEndedIterator for Dynamic<T> {
    /// Obtain the last initialized element.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]).into_iter();
    ///
    /// assert_eq!(actual.next_back(), Some(5));
    /// assert_eq!(actual.next_back(), Some(4));
    /// assert_eq!(actual.next_back(), Some(3));
    /// assert_eq!(actual.next_back(), Some(2));
    /// assert_eq!(actual.next_back(), Some(1));
    /// assert_eq!(actual.next_back(), Some(0));
    /// assert_eq!(actual.next_back(), None);
    /// ```
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.initialized > 0 {
            let ptr = self.buffer.as_ptr();

            // SAFETY: stays aligned within the allocated object.
            let ptr = unsafe { ptr.add(self.pre_capacity + self.initialized - 1) };

            self.initialized -= 1;
            self.post_capacity += 1;

            // SAFETY:
            // * `self.buffer` is non-null => `ptr` is non-null.
            // * The underlying `T` is initialized.
            Some(unsafe { (*ptr).assume_init_read() })
        } else {
            None
        }
    }
}

impl<'a, T: 'a + Clone> std::iter::FromIterator<T> for Dynamic<T> {
    /// Construct by moving elements from an iterator.
    ///
    /// # Panics
    /// The Rust runtime might `abort` if allocation fails, panics otherwise.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let mut actual = Dynamic::from_iter(expected.clone());
    ///
    /// assert!(actual.eq(expected))
    /// ```
    fn from_iter<Iter: IntoIterator<Item = T>>(iter: Iter) -> Self {
        let iter = iter.into_iter();

        let count = {
            let (min, max) = iter.size_hint();
            max.unwrap_or(min)
        };

        let mut instance = Dynamic::<T>::with_capacity(count).expect("successful allocation");

        instance.extend(iter);

        instance
    }
}

impl<T> std::iter::Extend<T> for Dynamic<T> {
    /// Append elements of an iterator in order.
    ///
    /// # Panics
    /// The Rust runtime might `abort` if allocation fails, panics otherwise.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let original = vec![0, 1, 2, 3, 4, 5];
    ///
    /// let mut expected = std::vec::Vec::from_iter(original.clone());
    /// let mut actual = Dynamic::from_iter(original.clone());
    ///
    /// expected.extend(original.clone());
    /// actual.extend(original.clone());
    ///
    /// assert!(actual.eq(expected))
    /// ```
    fn extend<Iter: IntoIterator<Item = T>>(&mut self, iter: Iter) {
        let mut iter = iter.into_iter();

        // SAFETY: `size_hint` can _NOT_ be trusted to exact size.
        let count = {
            let (min, max) = iter.size_hint();
            max.unwrap_or(min)
        };

        self.reserve(count).expect("successful allocation");

        while let Some(element) = iter.next() {
            if self.capacity() == 0 {
                self.reserve(1).expect("successful allocation");
            }

            let ptr = self.buffer.as_ptr();

            let offset = self.pre_capacity + self.initialized;

            // SAFETY: stays aligned within the allocated object.
            let ptr = unsafe { ptr.add(offset) };

            // SAFETY:
            // * `self.buffer` is non-null => `ptr` is non-null.
            // * the `MaybeUninit<T>` element is initialized.
            unsafe { (*ptr).write(element) };

            self.initialized += 1;
            self.post_capacity -= 1;
        }
    }
}

impl<T> std::default::Default for Dynamic<T> {
    /// Construct an instance with no elements and no capacity/allocation.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Collection;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let instance = Dynamic::<()>::default();
    ///
    /// assert_eq!(Collection::count(&instance), 0);
    /// assert_eq!(instance.capacity(), 0);
    /// ```
    fn default() -> Self {
        Self {
            buffer: std::ptr::NonNull::dangling(),
            pre_capacity: 0,
            initialized: 0,
            post_capacity: 0,
        }
    }
}

impl<T: Clone> Clone for Dynamic<T> {
    /// Construct an instance with no elements and no capacity/allocation.
    ///
    /// # Panics
    /// The Rust runtime might `abort` if allocation fails, panics otherwise.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let expected = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(expected.clone(), expected)
    /// ```
    fn clone(&self) -> Self {
        let mut clone = Self::with_capacity(self.count()).expect("successful allocation");

        clone.extend(self.iter().cloned());

        clone
    }
}

impl<T: std::cmp::PartialEq> std::cmp::PartialEq for Dynamic<T> {
    /// Query if the elements referenced to/contained are the same as `other`.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let left = [0, 1, 2, 3, 4, 5];
    /// let right = left.clone();
    ///
    /// let left = Dynamic::from_iter(left);
    /// let right = Dynamic::from_iter(right);
    ///
    /// assert_eq!(left, right);
    /// ```
    fn eq(&self, other: &Self) -> bool {
        if self.initialized != other.initialized {
            return false;
        }

        for index in 0..self.count() {
            if self[index] != other[index] {
                return false;
            }
        }

        true
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for Dynamic<T> {
    /// List the elements referenced to/contained.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Dynamic::from_iter(expected.iter());
    ///
    /// assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T> std::fmt::Pointer for Dynamic<T> {
    /// Display the underlying address pointed to.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let instance = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(format!("{instance:p}"), format!("{:p}", std::ptr::from_ref(&instance[0])));
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // SAFETY: the address of the pointer it read, not the pointer itself.
        std::fmt::Pointer::fmt(unsafe { &self.as_ptr() }, f)
    }
}

impl<'a, T: 'a> super::Collection<'a> for Dynamic<T> {
    type Element = T;

    /// Query the number of initialized elements contained.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::Collection;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let instance = Dynamic::from_iter(expected.clone());
    ///
    /// assert_eq!(Collection::count(&instance), expected.len());
    /// ```
    fn count(&self) -> usize {
        self.initialized
    }
}

impl<'a, T: 'a> Linear<'a> for Dynamic<T> {
    /// Create an immutable iterator over the initialized elements.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let expected = [0, 1, 2, 3, 4, 5];
    /// let actual = Dynamic::from_iter(expected.clone());
    ///
    /// for (actual, expected) in actual.iter().zip(expected.iter()) {
    ///     assert_eq!(actual, expected);
    /// }
    /// ```
    fn iter(&self) -> impl std::iter::DoubleEndedIterator<Item = &'a Self::Element> + std::iter::ExactSizeIterator + std::iter::FusedIterator {
        unsafe {
            // SAFETY: `MaybeUninit<T>` has the same memory layout as `T`.
            let ptr = self.buffer.cast::<T>().as_ptr();

            // SAFETY: stays aligned within the allocated object.
            let ptr = ptr.add(self.pre_capacity);

            // SAFETY: `self.buffer` is non-null => `ptr` is non-null
            let ptr = std::ptr::NonNull::new_unchecked(ptr);

            // SAFETY: `ptr` is dangling if and only if no elements have been
            // initialized, in which case the pointer will not be read.
            super::Iter::new(ptr, self.initialized)
        }
    }

    /// Create a mutable iterator over the initialized elements.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::Linear;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut expected = [0, 1, 2, 3, 4, 5];
    /// let mut actual = Dynamic::from_iter(expected.clone());
    ///
    /// for (actual, expected) in actual.iter_mut().zip(expected.iter_mut()) {
    ///     assert_eq!(actual, expected);
    /// }
    /// ```
    fn iter_mut(&mut self) -> impl std::iter::DoubleEndedIterator<Item = &'a mut Self::Element> + std::iter::ExactSizeIterator + std::iter::FusedIterator {
        unsafe {
            // SAFETY: `MaybeUninit<T>` has the same memory layout as `T`.
            let ptr = self.buffer.cast::<T>().as_ptr();

            // SAFETY: stays aligned within the allocated object.
            let ptr = ptr.add(self.pre_capacity);

            // SAFETY: `self.buffer` is non-null => `ptr` is non-null
            let ptr = std::ptr::NonNull::new_unchecked(ptr);

            // SAFETY: `ptr` is dangling if and only if no elements have been
            // initialized, in which case the pointer will not be read.
            super::IterMut::new(ptr, self.initialized)
        }
    }
}

impl<'a, T: 'a> Array<'a> for Dynamic<T> {
    /// Obtain an immutable pointer to the underlying contigious memory.
    ///
    /// The pointer starts at the first initialized element.
    ///
    /// # Safety
    /// * `self` must outlive the pointer.
    /// * The pointer must never be written to.
    /// * Modifying `self` might invalidate the pointer.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// let expected = std::ptr::from_ref(&instance[0]);
    /// let actual = unsafe { instance.as_ptr() };
    ///
    /// assert_eq!(actual, expected);
    /// ```
    unsafe fn as_ptr(&self) -> *const Self::Element {
        // SAFETY: `MaybeUninit<T>` has the same layout as `T`.
        self.buffer.cast::<T>().as_ptr().cast_const()
    }

    /// Obtain a mutable pointer to the underlying contigious memory.
    ///
    /// The pointer starts at the first initialized element.
    ///
    /// # Safety
    /// * `self` must outlive the pointer.
    /// * Modifying `self` might invalidate the pointer.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// let expected = std::ptr::from_ref(&instance[0]).cast_mut();
    /// let actual = unsafe { instance.as_mut_ptr() };
    ///
    /// assert_eq!(actual, expected);
    /// ```
    unsafe fn as_mut_ptr(&mut self) -> *mut Self::Element {
        // SAFETY: `MaybeUninit<T>` has the same layout as `T`.
        self.buffer.cast::<T>().as_ptr()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    mod with_capacity {
        use super::*;

        #[test]
        fn does_not_offset_buffer() {
            let actual = Dynamic::<usize>::with_capacity(256).expect("successful allocation");

            assert_eq!(actual.pre_capacity, 0);
        }

        #[test]
        fn does_not_initialize_elements() {
            let actual = Dynamic::<usize>::with_capacity(256).expect("successful allocation");

            assert_eq!(actual.initialized, 0);
        }

        #[test]
        fn increases_capacity() {
            const COUNT: usize = 256;

            let actual = Dynamic::<usize>::with_capacity(COUNT).expect("successful allocation");

            assert_eq!(actual.post_capacity, COUNT);
        }

        #[test]
        fn increases_capacity_for_zero_size_types() {
            const COUNT: usize = 256;

            let actual = Dynamic::<()>::with_capacity(COUNT).expect("successful allocation");

            assert_eq!(actual.post_capacity, COUNT);
        }

        #[test]
        fn allocates_capacity() {
            const COUNT: usize = 256;

            let actual = Dynamic::<usize>::with_capacity(COUNT).expect("successful allocation");

            for index in 0..COUNT {
                unsafe {
                    let ptr = actual.buffer.as_ptr().add(index);

                    // Ideally, this will seg-fault if we don't own the memory.
                    (*ptr).write(index);
                }
            }
        }

        #[test]
        fn allocated_zero_size_types() {
            const COUNT: usize = 256;

            let actual = Dynamic::<()>::with_capacity(COUNT).expect("successful allocation");

            assert_eq!(actual.post_capacity, COUNT);
        }

        #[test]
        fn does_not_allocate_when_zero() {
            let actual = Dynamic::<usize>::with_capacity(0).expect("successful allocation");

            assert_eq!(actual.post_capacity, 0);
        }
    }

    mod capacity {
        use super::*;

        #[test]
        fn is_reserved_element_count() {
            let actual = Dynamic::<usize>::with_capacity(256).expect("successful allocation");

            assert_eq!(actual.capacity(), actual.post_capacity);
        }

        #[test]
        fn does_not_count_pre_capacity() {
            let mut actual = Dynamic::<usize>::with_capacity(256).expect("successful allocation");

            std::mem::swap(&mut actual.pre_capacity, &mut actual.post_capacity);

            assert_eq!(actual.capacity(), actual.post_capacity);
        }

        #[test]
        fn specific_for_zero_size_types() {
            let actual = Dynamic::<()>::with_capacity(256).expect("successful allocation");

            assert_eq!(actual.capacity(), actual.post_capacity);
        }
    }

    mod reserve {
        use super::*;

        #[test]
        fn does_not_initialize_elements() {
            let mut actual = Dynamic::<usize>::default();
            actual.reserve(256).expect("successful allocation");

            assert_eq!(actual.initialized, 0);
        }

        #[test]
        fn increases_capacity() {
            const COUNT: usize = 256;

            let mut actual = Dynamic::<usize>::default();
            actual.reserve(COUNT).expect("successful allocation");

            assert_eq!(actual.post_capacity, COUNT);
        }

        #[test]
        fn increases_capacity_for_zero_size_types() {
            const COUNT: usize = 256;

            let mut actual = Dynamic::<usize>::default();
            actual.reserve(COUNT).expect("successful allocation");

            assert_eq!(actual.post_capacity, COUNT);
        }

        #[test]
        fn allocates_capacity() {
            const COUNT: usize = 256;

            let mut actual = Dynamic::<usize>::default();
            actual.reserve(COUNT).expect("successful allocation");

            for index in 0..COUNT {
                unsafe {
                    let ptr = actual.buffer.as_ptr().add(index);

                    // Ideally, this will seg-fault if we don't own the memory.
                    (*ptr).write(index);
                }
            }
        }

        #[test]
        fn reallocates_capacity() {
            const COUNT: usize = 256;

            let mut actual = Dynamic::<usize>::with_capacity(COUNT).expect("successful allocation");
            actual.reserve(COUNT * 2).expect("successful allocation");

            for index in 0..(COUNT * 2) {
                unsafe {
                    let ptr = actual.buffer.as_ptr().add(index);

                    // Ideally, this will seg-fault if we don't own the memory.
                    (*ptr).write(index);
                }
            }
        }

        #[test]
        fn does_not_modify_initialized_elements() {
            let expected = [0, 1, 2, 3, 4, 5];

            let mut actual = Dynamic::<usize>::from_iter(expected.iter().copied());
            actual.reserve(actual.len() * 16).expect("successful allocation");

            for index in 0..expected.len() {
                assert_eq!(actual[index], expected[index]);
            }
        }

        #[test]
        fn does_not_decrease_capacity() {
            let mut actual = Dynamic::<usize>::with_capacity(256).expect("successful allocation");

            actual.reserve(128).expect("already big enough");
            assert_ne!(actual.post_capacity, 128);

            actual.reserve(0).expect("already big enough");
            assert_ne!(actual.post_capacity, 0);
        }

        #[test]
        fn zero_capacity() {
            let mut actual = Dynamic::<usize>::with_capacity(0).expect("successful allocation");

            actual.reserve(0).expect("this should be a no-op");
        }
    }

    mod shrink {
        use super::*;

        #[test]
        fn does_not_initialize_elements() {
            let mut actual = Dynamic::<usize>::with_capacity(256).expect("successful allocation");

            actual.shrink(Some(128)).expect("successful reallocation");

            assert_eq!(actual.initialized, 0);
        }

        #[test]
        fn decreases_capacity() {
            let mut actual = Dynamic::<usize>::with_capacity(256).expect("successful allocation");

            actual.shrink(Some(128)).expect("successful reallocation");

            assert_eq!(actual.post_capacity, 128);
        }

        #[test]
        fn reallocates_capacity() {
            const COUNT: usize = 256;

            let mut actual = Dynamic::<usize>::with_capacity(COUNT).expect("successful allocation");

            actual.shrink(Some(COUNT/2)).expect("successful reallocation");

            for index in 0..(COUNT/2) {
                unsafe {
                    let ptr = actual.buffer.as_ptr().add(index);

                    // Ideally, this will seg-fault if we don't own the memory.
                    (*ptr).write(index);
                }
            }
        }

        #[test]
        fn does_not_modify_initialized_elements() {
            let expected = [0, 1, 2, 3, 4, 5];

            let mut actual: Dynamic<usize> = expected.iter().copied().collect();
            actual.reserve(expected.len() * 16).expect("successful allocation");

            actual.shrink(None).expect("successful reallocation");

            for index in 0..expected.len() {
                assert_eq!(actual[index], expected[index]);
            }
        }

        #[test]
        fn does_not_increase_capacity() {
            let mut actual: Dynamic<usize> = [0,1,2,3,4,5].into_iter().collect();

            actual.shrink(Some(256)).expect("already small enough");

            assert!(actual.post_capacity < 256);
        }

        #[test]
        fn zero_capacity() {
            let mut actual = Dynamic::<usize>::default();

            actual.shrink(None).expect("this should be a no-op");
        }
    }

    mod resize {
        use super::*;

        #[test]
        fn does_not_initialize_elements() {
            let mut actual = Dynamic::<usize>::default();

            actual.resize(256).expect("successful allocation");

            assert_eq!(actual.initialized, 0);
        }

        #[test]
        fn increases_capacity() {
            let mut actual = Dynamic::<usize>::default();

            actual.resize(77).expect("successful allocation");

            assert_eq!(actual.post_capacity, 77);
        }

        #[test]
        fn increases_capacity_for_zero_size_types() {
            let mut actual = Dynamic::<()>::default();

            actual.resize(77).expect("successful allocation");

            assert_eq!(actual.post_capacity, 77);
        }

        #[test]
        fn decreases_capacity() {
            let mut actual = Dynamic::<usize>::with_capacity(256).expect("successful allocation");

            actual.resize(77).expect("successful allocation");

            assert_eq!(actual.post_capacity, 77);
        }

        #[test]
        fn decreases_capacity_for_zero_size_types() {
            let mut actual = Dynamic::<()>::with_capacity(256).expect("successful allocation");

            actual.resize(77).expect("successful allocation");

            assert_eq!(actual.post_capacity, 77);
        }

        #[test]
        fn allocates_capacity() {
            let mut actual = Dynamic::<usize>::default();

            actual.resize(256).expect("successful reallocation");

            for index in 0..(256) {
                unsafe {
                    let ptr = actual.buffer.as_ptr().add(index);

                    // Ideally, this will seg-fault if we don't own the memory.
                    (*ptr).write(index);
                }
            }
        }

        #[test]
        fn reallocates_capacity() {
            const COUNT: usize = 256;

            let mut actual = Dynamic::<usize>::with_capacity(COUNT).expect("successful allocation");

            actual.resize(COUNT/2).expect("successful reallocation");

            for index in 0..(COUNT/2) {
                unsafe {
                    let ptr = actual.buffer.as_ptr().add(index);

                    // Ideally, this will seg-fault if we don't own the memory.
                    (*ptr).write(index);
                }
            }
        }

        #[test]
        fn does_not_modify_initialized_elements() {
            let expected = [0,1,2,3,4,5];
            let mut actual = Dynamic::from_iter(expected.iter().copied());

            actual.resize(0).expect("successful allocation");

            for index in 0..expected.len() {
                assert_eq!(actual[index], expected[index]);
            }
        }

        #[test]
        fn existing_capacity() {
            let mut actual = Dynamic::<usize>::with_capacity(256).expect("successful allocation");

            actual.resize(actual.capacity()).expect("already that size");
        }

        #[test]
        fn zero_capacity() {
            let mut actual = Dynamic::<usize>::default();

            actual.resize(0).expect("this should be a no-op");
        }
    }

    mod drop {
        use super::*;

        #[test]
        fn zero_size_type() {
            Dynamic::<()>::default();
        }

        #[test]
        fn empty() {
            Dynamic::<usize>::default();
        }

        #[test]
        fn all_initialized() {
            let mut instance = Dynamic::from_iter([0,1,2,3,4,5]);
            instance.shrink(None).expect("successful reallocation");
        }

        #[test]
        fn all_post_capacity() {
            Dynamic::<usize>::with_capacity(256).expect("successful allocation");
        }

        #[test]
        fn all_pre_capacity() {
            let mut actual = Dynamic::<usize>::with_capacity(256).expect("successful allocation");

            actual.pre_capacity = actual.post_capacity;
            actual.post_capacity = 0;
        }

        #[test]
        fn all() {
            let mut actual = Dynamic::<usize>::from_iter([0,1,2,3,4,5]);

            todo!("need a way to remove front elements");
        }
    }

    mod try_from {
        use super::*;

        #[test]
        fn allocates() {
            let expected = [0,1,2,3,4,5];

            let actual = Dynamic::try_from(expected.as_slice()).expect("successful allocation");

            for index in 0..expected.len() {
                unsafe {
                    let ptr = actual.buffer.as_ptr().add(index);

                    // Ideally, this will seg-fault if we don't own the memory.
                    (*ptr).write(index);
                }
            }
        }

        #[test]
        fn initializes_elements() {
            let expected = [0,1,2,3,4,5];

            let actual = Dynamic::try_from(expected.as_slice()).expect("successful allocation");

            for index in 0..expected.len() {
                assert_eq!(actual[index], expected[index]);
            }
        }

        #[test]
        fn initializes_state() {
            let expected = [0,1,2,3,4,5];
            let actual = Dynamic::try_from(expected.as_slice()).expect("successful allocation");

            assert_eq!(actual.pre_capacity, 0);
            assert_eq!(actual.initialized, expected.len());
        }
    }

    mod index {
        use super::*;
        use std::ops::Index;

        #[test]
        fn correct_element() {
            let expected = [0,1,2,3,4,5];
            let actual = Dynamic::from_iter(expected);

            for (index, expected) in expected.iter().enumerate() {
                assert_eq!(actual.index(index), expected);
            }
        }

        #[test]
        #[should_panic]
        fn panics_when_out_of_bounds() {
            let instance = Dynamic::<()>::default();

            instance.index(0);
        }
    }

    mod index_mut {
        use super::*;
        use std::ops::IndexMut;

        #[test]
        fn correct_element() {
            let expected = [0,1,2,3,4,5];
            let mut actual = Dynamic::from_iter(expected);

            for (index, expected) in expected.iter().enumerate() {
                assert_eq!(actual.index_mut(index), expected);
            }
        }

        #[test]
        #[should_panic]
        fn panics_when_out_of_bounds() {
            let mut instance = Dynamic::<()>::default();

            instance.index_mut(0);
        }
    }

    mod iterator {
        use super::*;

        #[test]
        fn count() {
            let expected = [0,1,2,3,4,5];
            let actual = Dynamic::from_iter(expected.iter().copied());

            assert_eq!(actual.iter().count(), expected.len());
        }

        #[test]
        fn is_front_element() {
            let expected = [0,1,2,3,4,5];
            let actual = Dynamic::from_iter(expected.iter().copied());

            assert!(actual.iter().eq(expected.iter()));
        }

        mod double_ended {
            use super::*;

            #[test]
            fn count() {
                let expected = [0,1,2,3,4,5];
                let actual = Dynamic::from_iter(expected.iter().copied());

                assert_eq!(actual.iter().rev().count(), expected.len());
            }

            #[test]
            fn is_back_element() {
                let expected = [0,1,2,3,4,5];
                let actual = Dynamic::from_iter(expected.iter().copied());

                assert!(actual.iter().rev().eq(expected.iter().rev()));
            }
        }

        mod exact_size {
            use super::*;

            #[test]
            fn hint() {
                let expected = [0,1,2,3,4,5];
                let actual = Dynamic::from_iter(expected.iter().copied());

                assert_eq!(actual.iter().size_hint(), (expected.len(), Some(expected.len())));
            }

            #[test]
            fn len() {
                let expected = [0,1,2,3,4,5];
                let actual = Dynamic::from_iter(expected.iter().copied());

                assert_eq!(actual.iter().len(), expected.len());
            }
        }

        mod fused {
            use super::*;

            #[test]
            fn empty() {
                let actual = Dynamic::<()>::default();
                let mut actual = actual.iter();

                // Yields `None` at least once.
                assert_eq!(actual.next(), None);
                assert_eq!(actual.next_back(), None);

                // Continues to yield `None`.
                assert_eq!(actual.next(), None);
                assert_eq!(actual.next_back(), None);
            }

            #[test]
            fn exhausted() {
                todo!()
            }
        }

        mod from {
            use super::*;

            #[test]
            fn allocates() {
                todo!()
            }

            #[test]
            fn initializes_elements() {
                todo!()
            }

            #[test]
            fn initializes_state() {
                todo!()
            }
        }

        mod extend {
            use super::*;

            #[test]
            fn allocates() {
                todo!()
            }

            #[test]
            fn reallocates() {
                todo!()
            }

            #[test]
            fn initializes_elements() {
                todo!()
            }

            #[test]
            fn initializes_state() {
                todo!()
            }
        }
    }

    mod default {
        use super::*;

        #[test]
        fn does_not_offset_buffer() {
            todo!()
        }

        #[test]
        fn does_not_initialize_elements() {
            todo!()
        }

        #[test]
        fn does_not_allocate() {
            todo!()
        }

        #[test]
        fn does_not_allocate_when_zero() {
            todo!()
        }
    }

    mod equality {
        use super::*;

        #[test]
        fn eq_when_same_elements() {
            todo!()
        }

        #[test]
        fn ne_when_different_elements() {
            todo!()
        }

        #[test]
        fn ignores_different_pre_capacity() {
            todo!()
        }

        #[test]
        fn ignores_different_post_capacity() {
            todo!()
        }

        #[test]
        fn symmetric() {
            todo!()
        }

        #[test]
        fn transitive() {
            todo!()
        }

        #[test]
        fn reflexive() {
            todo!()
        }
    }

    mod collection {
        use super::*;

        mod count {
            use super::*;

            #[test]
            fn initialized() {
                todo!()
            }

            #[test]
            fn zero_size_types() {
                todo!()
            }

            #[test]
            fn zero_when_empty() {
                todo!()
            }

            #[test]
            fn ignores_pre_capacity() {
                todo!()
            }

            #[test]
            fn ignores_post_capacity() {
                todo!()
            }
        }
    }

    mod linear {
        use super::*;

        mod iter {
            use super::*;

            #[test]
            fn count() {
                todo!()
            }

            #[test]
            fn in_order() {
                todo!()
            }
        }

        mod iter_mut {
            use super::*;

            #[test]
            fn count() {
                todo!()
            }

            #[test]
            fn in_order() {
                todo!()
            }
        }
    }

    mod array {
        use super::*;

        mod as_ptr {
            use super::*;

            #[test]
            fn correct_address() {
                todo!()
            }

            #[test]
            #[should_panic]
            fn panics_if_empty() {
                todo!()
            }
        }

        mod as_mut_ptr {
            use super::*;

            #[test]
            fn correct_address() {
                todo!()
            }

            #[test]
            #[should_panic]
            fn panics_if_empty() {
                todo!()
            }
        }

    }
}
