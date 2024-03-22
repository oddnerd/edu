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
            return Err(());
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

                    match std::alloc::Layout::array::<T>(elements) {
                        Ok(layout) => layout,
                        Err(_) => return Err(()),
                    }
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
    /// let instance = Dynamic::from([0, 1, 2, 3, 4, 5]);
    ///
    /// std::mem::drop(instance);
    /// ```
    fn drop(&mut self) {
        for index in 0..self.initialized {
            unsafe {
                // SAFETY: stays aligned within the allocated object.
                let ptr = self.buffer.as_ptr().add(index);

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
    /// todo!()
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
    /// todo!()
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
    /// todo!()
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
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// todo!()
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
    /// todo!()
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
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// todo!()
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
    /// todo!()
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
    /// todo!()
    /// ```
    fn extend<Iter: IntoIterator<Item = T>>(&mut self, iter: Iter) {
        let mut iter = iter.into_iter();

        let count = {
            let (min, max) = iter.size_hint();
            max.unwrap_or(min)
        };

        self.reserve(count).expect("successful allocation");

        while let Some(element) = iter.next() {
            let ptr = self.buffer.as_ptr();

            // SAFETY: stays aligned within the allocated object.
            let ptr = unsafe { ptr.add(self.pre_capacity + self.initialized) };

            // SAFETY:
            // * `self.buffer` is non-null => `ptr` is non-null.
            // * the `MaybeUninit<T>` element is initialized.
            unsafe { (*ptr).write(element) };
        }
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
    /// todo!()
    /// ```
    fn count(&self) -> usize {
        self.initialized
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
    /// todo!()
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
    /// todo!()
    /// ```
    fn clone(&self) -> Self {
        let mut clone = Self::with_capacity(self.count()).expect("successful allocation");

        clone.extend(self.iter().cloned());

        clone
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
    /// todo!()
    /// ```
    fn iter(&self) -> impl std::iter::Iterator<Item = &'a Self::Element> {
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
    /// todo!()
    /// ```
    fn iter_mut(&mut self) -> impl std::iter::Iterator<Item = &'a mut Self::Element> {
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
    /// todo!()
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
    /// todo!()
    /// ```
    unsafe fn as_mut_ptr(&mut self) -> *mut Self::Element {
        // SAFETY: `MaybeUninit<T>` has the same layout as `T`.
        self.buffer.cast::<T>().as_ptr()
    }
}

#[cfg(test)]
mod test {
    use super::*;
}
