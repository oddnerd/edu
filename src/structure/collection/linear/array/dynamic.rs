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
    /// if let Ok(instance) = Dynamic::<i32>::with_capacity(256) {
    ///     assert_eq!(Collection::count(&instance), 0);
    ///     assert_eq!(instance.capacity(), 256);
    ///     assert_eq!(instance.front_capacity(), 256);
    ///     assert_eq!(instance.back_capacity(), 256);
    /// } else {
    ///     panic!("allocation failed");
    /// }
    /// ```
    pub fn with_capacity(count: usize) -> Result<Self, ()> {
        let mut instance = Dynamic::<T>::default();

        match instance.resize(count) {
            Ok(_) => Ok(instance),
            Err(_) => Err(()),
        }
    }

    /// Query how many elements could be added without reallocation.
    ///
    /// Note that adding this many elements might still require rearranging the
    /// underlying buffer in non-constant time, however no memory reallocation
    /// will occur so pointers to elements remain valid.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::<()>::default();
    /// assert_eq!(instance.capacity(), 0);
    ///
    /// instance.reserve_back(256).expect("successful allocation");
    /// assert_eq!(instance.capacity(), 256);
    ///
    /// instance.reverse_front(256);
    /// assert_eq!(instance.capacity(), 512);
    /// ```
    pub fn capacity(&self) -> usize {
        // SAFETY: Global allocator API => addition cannot overflow.
        self.pre_capacity + self.post_capacity
    }

    /// How many elements can [`prepend`] in constant time/without reallocation.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// // Constructing with generic capacity.
    /// let mut instance = Dynamic::<usize>::with_capacity(256).unwrap();
    /// assert_eq!(instance.front_capacity(), 256);
    ///
    /// // Reserving for specific end of the buffer.
    /// instance.reserve_front(512).expect("successful allocation");
    /// assert_eq!(instance.front_capacity(), 512);
    ///
    /// // Reserving for wrong end of the buffer, but be empty.
    /// instance.reserve_back(1024).expect(successful allocation);
    /// assert_eq!(instance.front_capacity(), 1024);
    ///
    /// // That many elements can be prepended without invalidating pointers.
    /// let ptr = instance.as_ptr();
    /// for _ in 0..instance.back_capacity() {
    ///     assert!(instance.prepend(12345).is_ok()) // Cannot fail.
    /// }
    /// assert_eq!(instance.as_ptr(), ptr)
    /// ```
    pub fn front_capacity(&self) -> usize {
        if self.initialized == 0 {
            self.pre_capacity + self.post_capacity
        } else {
            self.pre_capacity
        }
    }

    /// How many elements can [`append`] in constant time/without reallocation.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// // Constructing with generic capacity.
    /// let mut instance = Dynamic::<usize>::with_capacity(256).unwrap();
    /// assert_eq!(instance.back_capacity(), 256);
    ///
    /// // Reserving for specific end of the buffer.
    /// instance.reserve_back(512).expect("successful allocation");
    /// assert_eq!(instance.back_capacity(), 512);
    ///
    /// // Reserving for wrong end of the buffer, but be empty.
    /// instance.reserve_front(1024).expect(successful allocation);
    /// assert_eq!(instance.back_capacity(), 1024);
    ///
    /// // That many elements can be appended without invalidating pointers.
    /// let ptr = instance.as_ptr();
    /// for _ in 0..instance.back_capacity() {
    ///     assert!(instance.append(12345).is_ok()) // Cannot fail.
    /// }
    /// assert_eq!(instance.as_ptr(), ptr)
    /// ```
    pub fn back_capacity(&self) -> usize {
        if self.initialized == 0 {
            self.pre_capacity + self.post_capacity
        } else {
            self.post_capacity
        }
    }

    /// Attempt to allocate space for at least `capacity` additional elements.
    ///
    /// In contrast to [`reserve_back`], this method will [`shift`] the
    /// elements to the front of the buffer to create space (thereby making
    /// [`capacity_front`] zero), (re)allocating if necessary to increase
    /// [`capacity_back`].
    ///
    /// This method increases the size of buffer by a geometric progression
    /// with a growth factor of two (2), hence the buffer could ideally contain
    /// a power of two (2) number of elements. This means it may allocate more
    /// memory than explicitly requested, but will attempt to recover when
    /// exactly `capacity` can be allocated, but not more.
    ///
    /// See also: [`reserve_front`] or [`reserve_back`] to reserve an exact
    /// amount of elements at a specific end of the buffer without [`shift`].
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
    /// let instance = Dynamic::<usize>::default();
    ///
    /// // From empty instance.
    /// instance.reserve(256).expect("successful allocation");
    ///
    /// // That many elements can be appended without invalidating pointers.
    /// let ptr = instance.as_ptr();
    /// for _ in 0..instance.capacity() {
    ///     assert!(instance.append(12345).is_ok()) // cannot fail.
    /// }
    /// assert_eq(instance.as_ptr(), ptr);
    ///
    /// // Shifts elements to consume capacity at the front of the buffer.
    /// instance.reserve_front(256).expect("successful allocation");
    /// let ptr = instance.as_ptr();
    /// assert!(instance.reserve(512).is_ok()); // No reallocation, just shift.
    /// for _ in 0..instance.capacity() {
    ///     assert!(instance.append(12345).is_ok()) // Cannot fail.
    /// }
    /// assert!(instance.as_ptr(), ptr);
    /// ```
    pub fn reserve(&mut self, capacity: usize) -> Result<&mut Self, ()> {
        let total_size = match self.initialized.checked_add(capacity) {
            Some(total) => total,
            None => return Err(()),
        };

        // See: https://en.wikipedia.org/wiki/Dynamic_array#Geometric_expansion_and_amortized_cost
        let size = match total_size.checked_next_power_of_two() {
            Some(increased_size) => increased_size,
            None => return Err(()),
        };

        let offset = isize::try_from(self.pre_capacity).expect("cannot exceed isize::MAX");
        self.shift(-offset).expect("cannot be out of bounds");

        self.reserve_back(capacity)
    }

    /// Allocate space for exactly `capacity` elements to be prepended.
    ///
    /// # Panics
    /// The Rust runtime might panic or otherwise `abort` if allocation fails.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let instance = Dynamic::<usize>::default();
    ///
    /// // From empty instance.
    /// instance.reserve_front(256).expect("successful allocation");
    ///
    /// // That many elements can be prepended without invalidating pointers.
    /// let ptr = instance.as_ptr();
    /// for _ in 0..instance.capacity() {
    ///     assert!(instance.prepend(12345).is_ok()) // cannot fail.
    /// }
    /// assert_eq(instance.as_ptr(), ptr);
    /// ```
    pub fn reserve_front(&mut self, capacity: usize) -> Result<&mut Self, ()> {
        todo!();
    }

    /// Allocate space for exactly `capacity` elements to be appended.
    ///
    /// # Panics
    /// The Rust runtime might panic or otherwise `abort` if allocation fails.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let instance = Dynamic::<usize>::default();
    ///
    /// // From empty instance.
    /// instance.reserve_back(256).expect("successful allocation");
    ///
    /// // That many elements can be prepended without invalidating pointers.
    /// let ptr = instance.as_ptr();
    /// for _ in 0..instance.capacity() {
    ///     assert!(instance.append(12345).is_ok()) // cannot fail.
    /// }
    /// assert_eq(instance.as_ptr(), ptr);
    /// ```
    pub fn reserve_back(&mut self, capacity: usize) -> Result<&mut Self, ()> {
        todo!();
    }

    /// Attempt to reduce [`capacity`] to exactly `capacity`, or none/zero.
    ///
    /// # Panics
    /// The Rust runtime might panic or otherwise `abort` if allocation fails.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    ///
    /// In contrast to [`shrink_back`], this method will [`shift`] the elements
    /// to the front of the buffer, _always_ shrinking [`capacity_front`] to
    /// zero, reallocating if necessary to decrease [`capacity_back`].
    ///
    /// See also: [`shrink_front`] or [`shrink_back`] to shrink a specific
    /// end of the buffer without shifting initialized elements.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::<usize>::with_capacity(256).expect("successful allocation");
    ///
    /// // Fill with elements.
    /// for element in 0..256 {
    ///     instance.append(element);
    /// }
    ///
    /// // Create capacity at the front.
    /// instance.reserve_front(256);
    ///
    /// // Shrink to have capacity of 128 elements at the back.
    /// instance.shrink(Some(128));
    /// assert_eq!(instance.capacity_front(), 0);
    /// assert_eq!(instance.capacity_back(), 128);
    ///
    /// // Shrink to have no capacity (shrink to fit).
    /// instance.shrink(None);
    /// assert_eq!(!instance.capacity_back(), 0);
    /// ```
    pub fn shrink(&mut self, capacity: Option<usize>) -> Result<&mut Self, ()> {
        todo!();

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

    /// Reallocate to reduce [`capacity_front`] to exactly `capacity` elements.
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
    /// let mut instance = Dynamic::<usize>::with_capacity(256).expect("successful allocation");
    ///
    /// // Half fill with elements.
    /// for element in 0..128 {
    ///     instance.prepend(element);
    /// }
    /// assert_eq!(instance.capacity_front(), 128);
    /// assert_eq!(instance.capacity_back(), 0);
    ///
    /// // Shrink to have capacity of 64 elements at the front.
    /// instance.shrink_front(Some(64));
    /// assert_eq!(instance.capacity_front(), 64);
    /// assert_eq!(instance.capacity_back(), 0);
    ///
    /// // Shrink to have no capacity (shrink to fit).
    /// instance.shrink_front(None);
    /// assert_eq!(instance.capacity_front(), 0);
    /// assert_eq!(instance.capacity_back(), 0);
    /// ```
    pub fn shrink_front(&mut self, capacity: Option<usize>) -> Result<&mut Self, ()> {
        todo!()
    }

    /// Reallocate to reduce back capacity to exactly `capacity` elements.
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
    /// let mut instance = Dynamic::<usize>::with_capacity(256).expect("successful allocation");
    ///
    /// // Half fill with elements.
    /// for element in 0..128 {
    ///     instance.append(element);
    /// }
    /// assert_eq!(instance.capacity_front(), 0);
    /// assert_eq!(instance.capacity_back(), 128);
    ///
    /// // Shrink to have capacity of 64 elements at the front.
    /// instance.shrink_back(Some(64));
    /// assert_eq!(instance.capacity_front(), 0);
    /// assert_eq!(instance.capacity_back(), 64);
    ///
    /// // Shrink to have no capacity (shrink to fit).
    /// instance.shrink_back(None);
    /// assert_eq!(instance.capacity_front(), 0);
    /// assert_eq!(instance.capacity_back(), 0);
    /// ```
    pub fn shrink_back(&mut self, capacity: Option<usize>) -> Result<&mut Self, ()> {
        todo!()
    }

    /// Shift the initialized elements `offset` positions within the buffer.
    ///
    /// The buffer first contains uninitialized pre-capacity, then initialized
    /// elements, and finally uninitialized post-capacity. This method maintains
    /// the order of initialized elements, but shifts them thereby converting
    /// some portion of the pre-capacity to post-capacity, or visa versa.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::<usize>::with_capacity(256).expect("successful allocation");
    ///
    /// // Fill with elements.
    /// for element in 0..256 {
    ///     instance.append(element);
    /// }
    ///
    /// // Allocate capacity at both ends.
    /// instance.reserve_front(256);
    /// instance.reserve_back(256);
    ///
    /// // Shift initialized elements to the front of the buffer.
    /// instance.shift(-256).expect("offset <= capacity_front()");
    /// instance.shift(-1).expect_err("offset out of bounds");
    /// assert_eq!(instance.capacity_front(), 0);
    /// assert_eq!(instance.capacity_front(), 256);
    ///
    /// // Shift initialized elements to the end of the buffer.
    /// instance.shift(512).expect("offset <= capacity_back()");
    /// instance.shift(1).expect_err("offset out of bounds");
    /// assert_eq!(instance.capacity_front(), 512);
    /// assert_eq!(instance.capacity_front(), 0);
    /// ```
    pub fn shift(&mut self, offset: isize) -> Result<&mut Self, ()> {
        if offset < 0 {
            if offset.unsigned_abs() > self.pre_capacity {
                return Err(());
            }

            self.pre_capacity -= offset.unsigned_abs();
            self.post_capacity += offset.unsigned_abs();
        } else if offset > 0 {
            if offset.unsigned_abs() > self.post_capacity {
                return Err(());
            }

            self.pre_capacity += offset.unsigned_abs();
            self.post_capacity -= offset.unsigned_abs();
        } else {
            debug_assert_eq!(offset, 0);

            return Ok(self);
        }

        unsafe {
            let source = self.as_mut_ptr();

            // SAFETY: aligned within the allocated object.
            let destination = source.offset(offset);

            // SAFETY:
            // * owned memory => source/destination valid for read/writes.
            // * no aliasing restrictions => source and destination can overlap.
            // * underlying buffer is aligned => both pointers are aligned.
            std::ptr::copy(source, destination, self.initialized);
        }

        Ok(self)
    }

    /// (Re)allocate the buffer to modify [`capacity_back`] by `capacity`.
    ///
    /// This method will increase [`capacity_back`] if `capacity` is positive,
    /// and decrease it if `capacity` is negative, (re)allocating if necessary.
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
    /// let mut instance = Dynamic::<usize>::default();
    ///
    /// // Cannot decrease zero capacity.
    /// assert_eq!(instance.capacity_back(), 0);
    /// instance.resize(-1).expect_err("no back capacity to resize");
    ///
    /// // Will do initial allocation.
    /// instance.resize(256).expect("successful allocation");
    /// assert_eq!(instance.capacity_front(), 0);
    /// assert_eq!(instance.capacity_back(), 256);
    ///
    /// // Will reallocate to increase capacity.
    /// instance.resize(256).expect("successful reallocation");
    /// assert_eq!(instance.capacity_front(), 0);
    /// assert_eq!(instance.capacity_back(), 512);
    ///
    /// // Will reallocate to reduce capacity.
    /// instance.resize(-256).expect("successful reallocation");
    /// assert_eq!(instance.capacity_front(), 0);
    /// assert_eq!(instance.capacity_back(), 256);
    /// ```
    fn resize(&mut self, capacity: isize) -> Result<&mut Self, ()> {
        // Treat all capacity as back capacity when empty.
        if self.initialized == 0 {
            self.post_capacity += self.pre_capacity;
            self.pre_capacity = 0;
        }

        let new_capacity = self.post_capacity.checked_add_signed(capacity).ok_or(())?;

        // Zero-size types do _NOT_ occupy memory, so no (re/de)allocation.
        if std::mem::size_of::<T>() == 0 {
            self.post_capacity = new_capacity;

            return Ok(self);
        }

        // SAFETY: the underlying global allocator API is limited to
        // allocations with `isize` length in bytes, hence the existing
        // allocation fits within `isize` elements so these additions
        // cannot overflow `usize`.`
        let offset = self.pre_capacity + self.initialized;
        let total = offset + self.post_capacity;

        let new_layout = {
            let total = offset.checked_add(new_capacity).ok_or(())?;

            match std::alloc::Layout::array::<T>(total) {
                Ok(layout) => layout,
                Err(_) => return Err(()),
            }
        };

        let ptr = {
            // No previous allocation exists, so create one.
            if total == 0 {
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
                let existing_layout = match std::alloc::Layout::array::<T>(total) {
                    Ok(layout) => layout,
                    Err(_) => return Err(()),
                };

                unsafe {
                    let ptr = self.buffer.as_ptr().cast::<u8>();

                    // Deallocate.
                    if offset == 0 && new_capacity == 0 {
                        // SAFETY:
                        // * `ptr` was allocated using the corresponding allocator.
                        // * `existing_layout` is currently allocated at `ptr`.
                        // * `new_layout` has non-zero size.
                        // * `Layout` guarantees `new_size.size() <= isize::MAX`.
                        std::alloc::dealloc(ptr, existing_layout);

                        // SAFETY: empty state => pointer will not read/write.
                        std::ptr::NonNull::<T>::dangling().as_ptr()
                    }
                    // Reallocate.
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

        self.post_capacity = new_capacity;

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
    fn try_from(slice: &'a [T]) -> Result<Self, Self::Error> {
        let mut instance = Self::with_capacity(slice.len())?;

        unsafe {
            // SAFETY: valid for reads up to `value.len()` elements.
            let source = slice.as_ptr();

            // SAFETY: `MaybeUninit<T>` has the same layout as `T`.
            let destination = instance.buffer.cast::<T>().as_ptr();

            // SAFETY:
            // * owned memory => destination valid for writes.
            // * no aliasing restrictions => source and destination can overlap.
            // * underlying buffer is aligned => both pointers are aligned.
            std::ptr::copy(source, destination, slice.len());
        }

        instance.initialized = slice.len();

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

impl<'a, T: 'a> std::iter::FromIterator<T> for Dynamic<T> {
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

        // Iterators may provide erroneous hints, so a smaller successful
        // allocation can occur later when inserting actual elements, otherwise
        // the error will be propagated once a necessary allocation fails.
        let mut instance = Dynamic::<T>::with_capacity(count).unwrap_or_default();

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

        // It is okay if this fails, later allocate for each individual element.
        let _ = self.reserve(count);

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
    fn iter(
        &self,
    ) -> impl std::iter::DoubleEndedIterator<Item = &'a Self::Element>
           + std::iter::ExactSizeIterator
           + std::iter::FusedIterator {
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
    fn iter_mut(
        &mut self,
    ) -> impl std::iter::DoubleEndedIterator<Item = &'a mut Self::Element>
           + std::iter::ExactSizeIterator
           + std::iter::FusedIterator {
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
    /// # Panics
    /// Will panic if there exists no allocation hence the pointer would be
    /// dangling and nothing meaningful can be derived from it. Note that a
    /// dangling (but nevertheless entirely useable in generic code) pointer
    /// _WILL_ be yielded for zero-size types.
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
        // If no allocation then the pointer is dangling and meaningless.
        assert!(self.pre_capacity + self.initialized + self.post_capacity > 0);

        // SAFETY: `MaybeUninit<T>` has the same layout as `T`.
        let ptr = self.buffer.cast::<T>().as_ptr().cast_const();

        // SAFETY: Stays aligned within the allocated object.
        ptr.add(self.pre_capacity)
    }

    /// Obtain a mutable pointer to the underlying contigious memory.
    ///
    /// The pointer starts at the first initialized element.
    ///
    /// # Safety
    /// * `self` must outlive the pointer.
    /// * Modifying `self` might invalidate the pointer.
    ///
    /// # Panics
    /// Will panic if there exists no allocation hence the pointer would be
    /// dangling and nothing meaningful can be derived from it. Note that a
    /// dangling (but nevertheless entirely useable in generic code) pointer
    /// _WILL_ be yielded for zero-size types.
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
        // If no allocation then the pointer is dangling and meaningless.
        assert!(self.pre_capacity + self.initialized + self.post_capacity > 0);

        // SAFETY: `MaybeUninit<T>` has the same layout as `T`.
        let ptr = self.buffer.cast::<T>().as_ptr();

        // SAFETY: Stays aligned within the allocated object.
        ptr.add(self.pre_capacity)
    }
}

impl<'a, T: 'a> crate::structure::collection::linear::list::List<'a> for Dynamic<T> {
    /// Insert an `element` at `index`.
    ///
    /// # Panics
    /// The Rust runtime might panic or otherwise `abort` if allocation fails.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::List;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::<usize>::default();
    ///
    /// instance.insert(0, 1);
    /// instance.insert(1, 3);
    /// instance.insert(1, 2);
    /// instance.insert(0, 0);
    ///
    /// assert!(instance.into_iter().eq([0, 1, 2, 3]));
    /// ```
    fn insert(
        &mut self,
        index: usize,
        element: Self::Element,
    ) -> Result<&mut Self::Element, Self::Element> {
        if index > self.initialized {
            return Err(element);
        }

        let mut ptr = self.buffer.as_ptr();

        if index == 0 && self.pre_capacity != 0 {
            // SAFETY: aligned within the allocated object.
            ptr = unsafe { ptr.add(self.pre_capacity - 1) };

            self.pre_capacity -= 1;
        } else if self.reserve(1).is_ok() {
            ptr = self.buffer.as_ptr();

            // Shift elements `[index..]` one position to the right.
            unsafe {
                // SAFETY: aligned within the allocated object.
                ptr = ptr.add(self.pre_capacity + index);

                // SAFETY: reserved memory => within the allocated object.
                let destination = ptr.add(1);

                // SAFETY:
                // * owned memory => source/destination valid for read/writes.
                // * no aliasing restrictions => source and destination can overlap.
                // * underlying buffer is aligned => both pointers are aligned.
                std::ptr::copy(ptr, destination, self.initialized - index);
            }

            self.post_capacity -= 1;
        } else {
            return Err(element);
        }

        self.initialized += 1;

        // SAFETY: the `MaybeUninit<T>` is initialized, even though the
        // underlying `T` is unutilized.
        Ok(unsafe { ptr.as_mut().unwrap_unchecked().write(element) })
    }

    /// Remove the element at `index`.
    ///
    /// # Performance
    /// This methods takes O(N) time and O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::List;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::from_iter([0,1,2,3,4,5]);
    ///
    /// instance.remove(5);
    /// instance.remove(2);
    /// instance.remove(0);
    ///
    /// assert!(instance.into_iter().eq([1, 3, 4]));
    /// ```
    fn remove(&mut self, index: usize) -> Option<Self::Element> {
        if index >= self.initialized {
            return None;
        }

        let element = unsafe {
            let ptr = self.buffer.as_ptr();

            // SAFETY: index within bounds => aligned within allocated object.
            let ptr = ptr.add(index);

            // SAFETY:
            // * owned memory => `ptr` is valid for reads.
            // * `MaybeUninit<T>` and underlying `T` are initialized.
            // * This takes ownership.
            ptr.read().assume_init()
        };

        unsafe {
            // SAFETY: aligned within the allocated object.
            let destination = self.buffer.as_ptr().add(index);

            // SAFETY:
            let source = destination.add(1);

            // SAFETY:
            // * owned memory => source/destination valid for read/writes.
            // * no aliasing restrictions => source and destination can overlap.
            // * underlying buffer is aligned => both pointers are aligned.
            std::ptr::copy(
                source,
                destination,
                self.initialized - self.pre_capacity - index,
            );
        }

        if index == 0 {
            self.pre_capacity += 1;
        } else {
            self.post_capacity += 1;
        }

        self.initialized -= 1;

        if self.initialized == 0 {
            self.post_capacity += self.pre_capacity;
            self.pre_capacity = 0;
        }

        Some(element)
    }

    /// Drop all initialized elements
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::list::List;
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::from_iter([0,1,2,3,4,5]);
    ///
    /// instance.clear();
    ///
    /// assert!(instance.initialized, 0);
    /// ```
    fn clear(&mut self) {
        let ptr = self.buffer.as_ptr();

        // SAFETY: initialized elements are after pre-capacity, so this stays
        // aligned within the allocation object pointing to the first
        // initialized element, if there exists one.
        let ptr = unsafe { ptr.add(self.pre_capacity) };

        for index in 0..self.initialized {
            // SAFETY: stays aligned within the allocated object.
            let ptr = unsafe { ptr.add(index) };

            unsafe { (*ptr).assume_init_drop() };
        }

        self.initialized = 0;
        self.post_capacity += self.pre_capacity;
        self.pre_capacity = 0;
    }
}

#[cfg(test)]
mod test {
    use super::*;

    mod method {
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

                let mut actual =
                    Dynamic::<usize>::with_capacity(COUNT).expect("successful allocation");

                for index in 0..COUNT {
                    unsafe {
                        let ptr = actual.as_mut_ptr().add(index);

                        // Ideally, this will seg-fault if we don't own the memory.
                        ptr.write(index);
                    }
                }
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
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

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
                        let ptr = actual.as_mut_ptr().add(index);

                        // Ideally, this will seg-fault if we don't own the memory.
                        ptr.write(index);
                    }
                }
            }

            #[test]
            fn reallocates_capacity() {
                const COUNT: usize = 256;

                let mut actual =
                    Dynamic::<usize>::with_capacity(COUNT).expect("successful allocation");
                actual.reserve(COUNT * 2).expect("successful allocation");

                for index in 0..(COUNT * 2) {
                    unsafe {
                        let ptr = actual.as_mut_ptr().add(index);

                        // Ideally, this will seg-fault if we don't own the memory.
                        ptr.write(index);
                    }
                }
            }

            #[test]
            fn does_not_modify_initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual = Dynamic::<usize>::from_iter(expected.iter().copied());
                actual
                    .reserve(actual.len() * 16)
                    .expect("successful allocation");

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn does_not_decrease_capacity() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                actual.reserve(128).expect("already big enough");
                assert_ne!(actual.post_capacity, 128);

                actual.reserve(0).expect("already big enough");
                assert_ne!(actual.post_capacity, 0);
            }

            #[test]
            fn does_nothing_when_zero_capacity() {
                let mut actual = Dynamic::<usize>::with_capacity(0).expect("successful allocation");

                actual.reserve(0).expect("this should be a no-op");
            }
        }

        mod shrink {
            use super::*;

            #[test]
            fn does_not_initialize_elements() {
                const COUNT: usize = 256;

                let mut actual =
                    Dynamic::<usize>::with_capacity(COUNT).expect("successful allocation");

                actual
                    .shrink(Some(COUNT / 2))
                    .expect("successful reallocation");

                assert_eq!(actual.initialized, 0);
            }

            #[test]
            fn decreases_capacity() {
                const COUNT: usize = 256;

                let mut actual =
                    Dynamic::<usize>::with_capacity(COUNT).expect("successful allocation");

                actual
                    .shrink(Some(COUNT / 2))
                    .expect("successful reallocation");

                assert_eq!(actual.post_capacity, 128);
            }

            #[test]
            fn reallocates_capacity() {
                const COUNT: usize = 256;

                let mut actual =
                    Dynamic::<usize>::with_capacity(COUNT).expect("successful allocation");

                actual
                    .shrink(Some(COUNT / 2))
                    .expect("successful reallocation");

                for index in 0..(COUNT / 2) {
                    unsafe {
                        let ptr = actual.as_mut_ptr().add(index);

                        // Ideally, this will seg-fault if we don't own the memory.
                        ptr.write(index);
                    }
                }
            }

            #[test]
            fn does_not_modify_initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual: Dynamic<usize> = expected.iter().copied().collect();
                actual
                    .reserve(expected.len() * 2)
                    .expect("successful allocation");

                actual.shrink(None).expect("successful reallocation");

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn does_not_increase_capacity() {
                let mut actual: Dynamic<usize> = [0, 1, 2, 3, 4, 5].into_iter().collect();

                actual
                    .shrink(Some(actual.len() * 2))
                    .expect("already small enough");

                assert!(actual.post_capacity < 256);
            }

            #[test]
            fn does_nothing_when_zero_capacity() {
                let mut actual = Dynamic::<()>::default();

                actual.shrink(None).expect("this should be a no-op");
            }

            #[test]
            fn deallocates_when_empty() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                actual.shrink(None).expect("successful deallocation");

                assert_eq!(actual.pre_capacity, 0);
                assert_eq!(actual.post_capacity, 0);
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
                const COUNT: usize = 77;

                let mut actual = Dynamic::<usize>::default();

                actual.resize(COUNT).expect("successful allocation");

                assert_eq!(actual.post_capacity, COUNT);
            }

            #[test]
            fn increases_capacity_for_zero_size_types() {
                const COUNT: usize = 77;

                let mut actual = Dynamic::<()>::default();

                actual.resize(COUNT).expect("successful allocation");

                assert_eq!(actual.post_capacity, COUNT);
            }

            #[test]
            fn decreases_capacity() {
                const COUNT: usize = 256;

                let mut actual =
                    Dynamic::<usize>::with_capacity(COUNT).expect("successful allocation");

                actual.resize(COUNT / 2).expect("successful allocation");

                assert_eq!(actual.post_capacity, COUNT / 2);
            }

            #[test]
            fn decreases_capacity_for_zero_size_types() {
                const COUNT: usize = 256;

                let mut actual =
                    Dynamic::<()>::with_capacity(COUNT / 2).expect("successful allocation");

                actual.resize(COUNT / 2).expect("successful allocation");

                assert_eq!(actual.post_capacity, COUNT / 2);
            }

            #[test]
            fn allocates_capacity() {
                const COUNT: usize = 256;

                let mut actual = Dynamic::<usize>::default();

                actual.resize(COUNT).expect("successful reallocation");

                for index in 0..COUNT {
                    unsafe {
                        let ptr = actual.as_mut_ptr().add(index);

                        // Ideally, this will seg-fault if we don't own the memory.
                        ptr.write(index);
                    }
                }
            }

            #[test]
            fn reallocates_capacity() {
                const COUNT: usize = 256;

                let mut actual =
                    Dynamic::<usize>::with_capacity(COUNT).expect("successful allocation");

                actual.resize(COUNT / 2).expect("successful reallocation");

                for index in 0..(COUNT / 2) {
                    unsafe {
                        let ptr = actual.as_mut_ptr().add(index);

                        // Ideally, this will seg-fault if we don't own the memory.
                        ptr.write(index);
                    }
                }
            }

            #[test]
            fn does_not_modify_initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                actual.resize(0).expect("successful allocation");

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn does_nothing_when_existing_capacity() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                actual.resize(actual.capacity()).expect("already that size");
            }

            #[test]
            fn does_nothing_when_zero_capacity() {
                let mut actual = Dynamic::<usize>::default();

                actual.resize(0).expect("this should be a no-op");
            }

            #[test]
            fn deallocates_when_empty() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                actual.resize(0).expect("successful deallocation");

                assert_eq!(actual.pre_capacity, 0);
                assert_eq!(actual.post_capacity, 0);
            }
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
            let mut instance = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
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
            let mut actual = Dynamic::<usize>::from_iter([0, 1, 2, 3, 4, 5]);

            // allocate post-capacity
            actual.reserve(256).expect("successful allocation");

            // make pre-capacity
            use crate::structure::collection::linear::list::List;
            actual.remove(0);
            actual.remove(0);
        }
    }

    mod try_from {
        use super::*;

        #[test]
        fn does_not_offset_buffer() {
            let expected = [0, 1, 2, 3, 4, 5];
            let actual = Dynamic::try_from(expected.as_slice()).expect("successful allocation");

            assert_eq!(actual.pre_capacity, 0);
        }

        #[test]
        fn has_elements() {
            let expected = [0, 1, 2, 3, 4, 5];
            let actual = Dynamic::try_from(expected.as_slice()).expect("successful allocation");

            assert_eq!(actual.initialized, expected.len());
        }

        #[test]
        fn allocates() {
            let expected = [0, 1, 2, 3, 4, 5];

            let mut actual = Dynamic::try_from(expected.as_slice()).expect("successful allocation");

            for index in 0..expected.len() {
                unsafe {
                    let ptr = actual.as_mut_ptr().add(index);

                    // Ideally, this will seg-fault if we don't own the memory.
                    ptr.write(index);
                }
            }
        }

        #[test]
        fn initializes_elements() {
            let expected = [0, 1, 2, 3, 4, 5];

            let actual = Dynamic::try_from(expected.as_slice()).expect("successful allocation");

            for index in 0..expected.len() {
                assert_eq!(actual[index], expected[index]);
            }
        }
    }

    mod index {
        use super::*;
        use std::ops::Index;

        #[test]
        fn correct_element() {
            let expected = [0, 1, 2, 3, 4, 5];
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
            let mut expected = [0, 1, 2, 3, 4, 5];
            let mut actual = Dynamic::from_iter(expected);

            for (index, expected) in expected.iter_mut().enumerate() {
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

        mod into {
            use super::*;

            #[test]
            fn element_count() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Dynamic::from_iter(expected.iter().copied());

                assert_eq!(actual.into_iter().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Dynamic::from_iter(expected.iter().copied());

                assert!(actual.into_iter().eq(expected.into_iter()));
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Dynamic::from_iter(expected.iter().copied());

                    assert_eq!(actual.into_iter().rev().count(), expected.len());
                }

                #[test]
                fn in_order() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Dynamic::from_iter(expected.iter().copied());

                    assert!(actual.into_iter().rev().eq(expected.into_iter().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Dynamic::from_iter(expected.iter().copied());

                    assert_eq!(
                        actual.into_iter().size_hint(),
                        (expected.len(), Some(expected.len()))
                    );
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Dynamic::from_iter(expected.iter().copied());

                    assert_eq!(actual.into_iter().len(), expected.len());
                }
            }

            mod fused {
                use super::*;

                #[test]
                fn empty() {
                    let actual = Dynamic::<()>::default();
                    let mut actual = actual.into_iter();

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }

                #[test]
                fn exhausted() {
                    let actual = Dynamic::from_iter([()].iter());
                    let mut actual = actual.into_iter();

                    // Exhaust the elements.
                    actual.next();

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }
            }
        }

        mod from {
            use super::*;

            #[test]
            fn does_not_offset_buffer() {
                let actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5].iter().copied());

                assert_eq!(actual.pre_capacity, 0);
            }

            #[test]
            fn has_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Dynamic::from_iter(expected.iter().copied());

                assert_eq!(actual.initialized, expected.len());
            }

            #[test]
            fn allocates() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                for index in 0..expected.len() {
                    unsafe {
                        let ptr = actual.as_mut_ptr().add(index);

                        // Ideally, this will seg-fault if we don't own the memory.
                        ptr.write(index);
                    }
                }
            }

            #[test]
            fn initializes_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Dynamic::from_iter(expected.iter().copied());

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn empty() {
                let actual = Dynamic::<()>::from_iter(std::iter::empty());

                assert_eq!(actual.pre_capacity, 0);
                assert_eq!(actual.initialized, 0);
                assert_eq!(actual.post_capacity, 0);
            }

            struct Iter<I> {
                data: std::iter::Copied<I>,
            }

            impl<'a, T: 'a + Copy, I> Iterator for Iter<I>
            where
                I: Iterator<Item = &'a T>,
            {
                type Item = T;
                fn next(&mut self) -> Option<Self::Item> {
                    self.data.next()
                }

                fn size_hint(&self) -> (usize, Option<usize>) {
                    (isize::MAX as usize, Some(isize::MAX as usize))
                }
            }

            #[test]
            fn does_not_trust_size_hint() {
                let expected = [0, 1, 2, 3, 4, 5];

                // Ideally, this will panic if it uses the invalid size.
                let actual = Dynamic::from_iter(Iter {
                    data: expected.iter().copied(),
                });

                assert!(actual.into_iter().eq(expected.into_iter()));
            }
        }

        mod extend {
            use super::*;

            #[test]
            fn has_elements() {
                let mut actual = Dynamic::default();

                let expected = [0, 1, 2, 3, 4, 5];
                actual.extend(expected.iter().copied());

                assert_eq!(actual.initialized, expected.len());
            }

            #[test]
            fn initializes_elements() {
                let mut actual = Dynamic::default();

                let expected = [0, 1, 2, 3, 4, 5];
                actual.extend(expected.iter().copied());

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn inserts_after_initialized_elements() {
                let initialized = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(initialized.iter().copied());

                let expected = [6, 7, 8, 9, 10];
                actual.extend(expected.iter().copied());

                for index in initialized.len()..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn does_not_modify_initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                actual.extend([6, 7, 8, 9, 10]);

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn does_nothing_if_empty_iterator() {
                let mut actual = Dynamic::<()>::default();

                actual.extend(std::iter::empty());

                assert_eq!(actual.pre_capacity, 0);
                assert_eq!(actual.initialized, 0);
                assert_eq!(actual.post_capacity, 0);
            }
        }
    }

    mod default {
        use super::*;

        #[test]
        fn does_not_offset_buffer() {
            let actual = Dynamic::<()>::default();

            assert_eq!(actual.pre_capacity, 0);
        }

        #[test]
        fn does_not_initialize_elements() {
            let actual = Dynamic::<()>::default();

            assert_eq!(actual.initialized, 0);
        }

        #[test]
        fn does_not_allocate() {
            let actual = Dynamic::<()>::default();

            assert_eq!(actual.post_capacity, 0);
        }
    }

    mod clone {
        use super::*;

        #[test]
        fn does_not_offset_buffer() {
            let expected = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

            let actual = expected.clone();

            assert_eq!(actual.pre_capacity, 0);
        }

        #[test]
        fn has_elements() {
            let expected = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

            let actual = expected.clone();

            assert_eq!(actual.initialized, expected.len());
        }

        #[test]
        fn is_equivalent() {
            let expected = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

            let actual = expected.clone();

            assert_eq!(actual, expected);
        }
    }

    mod equality {
        use super::*;

        #[test]
        fn eq_when_same_elements() {
            let expected = [0, 1, 2, 3, 4, 5];

            let first = Dynamic::from_iter(expected.iter().copied());
            let second = Dynamic::from_iter(expected.iter().copied());

            assert_eq!(first, second);
        }

        #[test]
        fn ne_when_different_elements() {
            let first = Dynamic::from_iter([0]);
            let second = Dynamic::from_iter([1]);

            assert_ne!(first, second);
        }

        #[test]
        fn ignores_different_pre_capacity() {
            let first = Dynamic::<()>::with_capacity(256).expect("successful allocation");
            let mut second = Dynamic::<()>::with_capacity(256).expect("successful allocation");

            std::mem::swap(&mut second.pre_capacity, &mut second.post_capacity);

            assert_eq!(first, second);
        }

        #[test]
        fn ignores_different_post_capacity() {
            let expected = [0, 1, 2, 3, 4, 5];

            let first = Dynamic::from_iter(expected.iter().copied());
            let mut second = Dynamic::from_iter(expected.iter().copied());

            second
                .reserve(expected.len() * 2)
                .expect("successful allocation");

            assert_eq!(first, second);
        }

        #[test]
        fn is_symmetric() {
            let expected = [0, 1, 2, 3, 4, 5];

            let first = Dynamic::from_iter(expected.iter().copied());
            let second = Dynamic::from_iter(expected.iter().copied());

            // `first == second` <=> `second == first`
            assert_eq!(first, second);
            assert_eq!(second, first);
        }

        #[test]
        fn is_transitive() {
            let expected = [0, 1, 2, 3, 4, 5];

            let first = Dynamic::from_iter(expected.iter().copied());
            let second = Dynamic::from_iter(expected.iter().copied());
            let third = Dynamic::from_iter(expected.iter().copied());

            // `first == second && second == third` => `first == third`
            assert_eq!(first, second);
            assert_eq!(second, third);
            assert_eq!(third, first);
        }

        #[test]
        fn is_reflexive() {
            let actual = Dynamic::<()>::default();

            assert_eq!(actual, actual);
        }
    }

    mod collection {
        use super::*;

        mod count {
            use super::*;

            #[test]
            fn initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Dynamic::from_iter(expected.iter().copied());

                assert_eq!(actual.initialized, expected.len());
                assert_eq!(Collection::count(&actual), expected.len());
            }

            #[test]
            fn zero_when_empty() {
                let actual = Dynamic::<()>::default();

                assert_eq!(Collection::count(&actual), 0);
            }

            #[test]
            fn ignores_pre_capacity() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual = Dynamic::from_iter(expected.iter().copied());

                use crate::structure::collection::linear::list::List;
                actual.remove(0);

                assert_eq!(actual.count(), expected.len() - 1);
            }

            #[test]
            fn ignores_post_capacity() {
                let mut actual = Dynamic::<()>::default();

                actual.reserve(256).expect("successful allocation");

                assert_eq!(Collection::count(&actual), 0);
            }
        }
    }

    mod linear {
        use super::*;

        mod iter {
            use super::*;

            #[test]
            fn element_count() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Dynamic::from_iter(expected.iter().copied());

                assert_eq!(actual.iter().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Dynamic::from_iter(expected.iter().copied());

                assert!(actual.iter().eq(expected.iter()));
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Dynamic::from_iter(expected.iter().copied());

                    assert_eq!(actual.iter().rev().count(), expected.len());
                }

                #[test]
                fn in_order() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Dynamic::from_iter(expected.iter().copied());

                    assert!(actual.iter().rev().eq(expected.iter().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let actual = Dynamic::from_iter(expected.iter().copied());

                    assert_eq!(
                        actual.iter().size_hint(),
                        (expected.len(), Some(expected.len()))
                    );
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];
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
                    let actual = Dynamic::from_iter([()].iter());
                    let mut actual = actual.iter();

                    // Exhaust the elements.
                    actual.next();

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }
            }
        }

        mod iter_mut {
            use super::*;

            #[test]
            fn element_count() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                assert_eq!(actual.iter_mut().count(), expected.len());
            }

            #[test]
            fn in_order() {
                let mut expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                assert!(actual.iter_mut().eq(expected.iter_mut()));
            }

            mod double_ended {
                use super::*;

                #[test]
                fn element_count() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let mut actual = Dynamic::from_iter(expected.iter().copied());

                    assert_eq!(actual.iter_mut().rev().count(), expected.len());
                }

                #[test]
                fn in_order() {
                    let mut expected = [0, 1, 2, 3, 4, 5];
                    let mut actual = Dynamic::from_iter(expected.iter().copied());

                    assert!(actual.iter_mut().rev().eq(expected.iter_mut().rev()));
                }
            }

            mod exact_size {
                use super::*;

                #[test]
                fn hint() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let mut actual = Dynamic::from_iter(expected.iter().copied());

                    assert_eq!(
                        actual.iter_mut().size_hint(),
                        (expected.len(), Some(expected.len()))
                    );
                }

                #[test]
                fn len() {
                    let expected = [0, 1, 2, 3, 4, 5];
                    let mut actual = Dynamic::from_iter(expected.iter().copied());

                    assert_eq!(actual.iter_mut().len(), expected.len());
                }
            }

            mod fused {
                use super::*;

                #[test]
                fn empty() {
                    let mut actual = Dynamic::<()>::default();
                    let mut actual = actual.iter_mut();

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }

                #[test]
                fn exhausted() {
                    let mut actual = Dynamic::from_iter([()].iter());
                    let mut actual = actual.iter_mut();

                    // Exhaust the elements.
                    actual.next();

                    // Yields `None` at least once.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);

                    // Continues to yield `None`.
                    assert_eq!(actual.next(), None);
                    assert_eq!(actual.next_back(), None);
                }
            }
        }
    }

    mod array {
        use super::*;

        mod as_ptr {
            use super::*;

            #[test]
            fn correct_address() {
                let actual = Dynamic::<i32>::from_iter([0, 1, 2, 3, 4, 5]);

                assert_eq!(
                    unsafe { actual.as_ptr() },
                    actual.buffer.as_ptr().cast::<i32>().cast_const()
                );
            }

            #[test]
            #[should_panic]
            fn panics_if_no_allocation() {
                let actual = Dynamic::<()>::default();

                unsafe { actual.as_ptr() };
            }
        }

        mod as_mut_ptr {
            use super::*;

            #[test]
            fn correct_address() {
                let mut actual = Dynamic::<i32>::from_iter([0, 1, 2, 3, 4, 5]);

                assert_eq!(
                    unsafe { actual.as_mut_ptr() },
                    actual.buffer.as_ptr().cast::<i32>()
                );
            }

            #[test]
            #[should_panic]
            fn panics_if_no_allocation() {
                let mut actual = Dynamic::<()>::default();

                unsafe { actual.as_mut_ptr() };
            }
        }
    }

    mod list {
        use super::*;
        use crate::structure::collection::linear::list::List;

        mod insert {
            use super::*;

            #[test]
            fn adds_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                actual.insert(2, 256).expect("successful allocation");

                assert_eq!(actual.initialized, expected.len() + 1);
            }

            #[test]
            fn initializes_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                actual.insert(2, 256).expect("successful allocation");

                assert_eq!(actual[2], 256);
            }

            #[test]
            fn yields_inserted_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                let actual = actual.insert(2, 256).expect("successful allocation");

                assert_eq!(actual, &mut 256);
            }

            #[test]
            fn does_not_modify_leading_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                const INDEX: usize = 2;
                actual.insert(INDEX, 256).expect("successful allocation");

                for index in 0..INDEX {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn does_not_modify_trailing_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                const INDEX: usize = 2;
                actual.insert(INDEX, 256).expect("successful allocation");

                for index in INDEX..expected.len() {
                    assert_eq!(actual[index + 1], expected[index]);
                }
            }

            #[test]
            fn will_reserve_capacity() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                actual.shrink(None).expect("successful allocation");

                let actual = actual.insert(2, 12345);

                assert!(actual.is_ok());
            }

            #[test]
            fn can_append() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                actual.insert(6, 12345).expect("successful allocation");

                assert_eq!(actual[6], 12345);
            }

            #[test]
            fn appending_consumes_post_capacity() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());
                actual.reserve(1).expect("successful allocation");

                let capacity = actual.post_capacity;

                actual.insert(6, 12345).expect("successful allocation");

                assert_eq!(actual.post_capacity, capacity - 1);
            }

            #[test]
            fn can_prepend() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                actual.insert(0, 12345).expect("successful allocation");

                assert_eq!(actual[0], 12345);
            }

            #[test]
            fn prepending_consumes_pre_capacity() {
                let expected = [-1, 0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                actual.remove(0);

                let capacity = actual.pre_capacity;

                actual.insert(0, -1).expect("uses pre-capacity");

                assert_eq!(actual.pre_capacity, capacity - 1);
            }

            #[test]
            fn when_empty() {
                let mut actual = Dynamic::<usize>::default();

                actual.insert(0, 256).expect("successful allocation");

                assert_eq!(actual[0], 256);
            }
        }

        mod remove {
            use super::*;

            #[test]
            fn subtracts_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                actual.remove(0);

                assert_eq!(actual.initialized, expected.len() - 1);
            }

            #[test]
            fn yields_element() {
                let expected = [0, 1, 2, 3, 4, 5, 256];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                let actual = actual.remove(6);

                assert_eq!(actual.unwrap(), 256);
            }

            #[test]
            fn does_not_modify_leading_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                const INDEX: usize = 2;
                actual.remove(INDEX);

                for index in 0..INDEX {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn does_not_modify_trailing_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                const INDEX: usize = 2;
                actual.remove(INDEX);

                // [0, 1, 2, 3, 4, 5]
                // [0, 1, 3, 4, 5]

                for index in INDEX..expected.len() - 1 {
                    assert_eq!(actual[index], expected[index + 1]);
                }
            }

            #[test]
            fn none_when_index_out_of_bounds() {
                let mut actual = Dynamic::<()>::default();

                let actual = actual.remove(0);

                assert!(actual.is_none());
            }
        }

        mod clear {
            use super::*;

            #[test]
            fn uninitialized_all_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                actual.clear();

                assert_eq!(actual.initialized, 0);
            }
        }
    }
}
