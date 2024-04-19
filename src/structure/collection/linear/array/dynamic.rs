//! Implementation of [`Dynamic`].

use super::super::List;
use super::Array;
use super::Collection;
use super::Linear;

/// An [`Array`] which can store a runtime defined number of elements.
///
/// This is (mostly) equivalent to Rust's [`Vec`] or C++'s `std::vector`.
///
/// Contigious memory is heap-allocated with alignment and size to store
/// elements of type `T`, referred to as the buffer. The front of the buffer
/// (potentially) contains uninitialized elements, then all initialized
/// elements in the order they were inserted, and finally at the back
/// (potentially) other uninitialized elements.
///
/// The term 'capacity' refers to pre-allocated memory containing those
/// uninitialized elements into which new elements can be added without
/// additional memory allocation. This means [`Self::capacity`] elements can be
/// [`Self::insert`] without invalidating pointers to the buffer. Note that
/// pointers to specific elements may no longer point to the same element/point
/// to an uninitialized element as the pre-existing elements may be moved
/// within the buffer (maintaining order, see [`Self::shift`]) to utilize said
/// capacity. In contrast, using end-specific capacity via [`Self::prepend`] or
/// [`Self::append`] alongside [`Self::capacity_back`] or
/// [`Self::capacity_back`] _will_ maintain pointers to specific elements.
///
/// Capacity may be manually allocated via [`Self::with_capacity`] and
/// [`Self::reserve`], or end-specific [`Self::reserve_front`] and
/// [`Self::reserve_back`] methods which will reallocate thereby invaliding all
/// pointers. Furthermore, capacity can be deallocated (retaining initialized
/// elements) via [`Self::shrink`], or end-specific [`Self::shrink_front`]
/// and [`Self::shrink_back`]. Shrinking when no elements are initialized will
/// deallocate freeing all memory.
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
    ///     assert_eq!(instance.capacity_front(), 256);
    ///     assert_eq!(instance.capacity_back(), 256);
    /// } else {
    ///     panic!("allocation failed");
    /// }
    /// ```
    pub fn with_capacity(count: usize) -> Result<Self, FailedAllocation> {
        let mut instance = Dynamic::<T>::default();

        match instance.reserve_back(count) {
            Ok(_) => Ok(instance),
            Err(_) => Err(FailedAllocation),
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
    /// let mut instance = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    /// assert_eq!(instance.capacity(), 0);
    ///
    /// instance.reserve_back(256).expect("successful allocation");
    /// assert_eq!(instance.capacity(), 256);
    ///
    /// instance.reserve_front(256);
    /// assert_eq!(instance.capacity(), 512);
    /// ```
    pub fn capacity(&self) -> usize {
        // SAFETY: Global allocator API => addition cannot overflow.
        self.pre_capacity + self.post_capacity
    }

    /// How many elements can [`Self::prepend`] in constant time/without reallocation.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::list::List;
    ///
    /// // Constructing with generic capacity.
    /// let mut instance = Dynamic::<usize>::with_capacity(256).unwrap();
    /// assert_eq!(instance.capacity_front(), 256);
    ///
    /// // Reserving for specific end of the buffer.
    /// instance.reserve_front(512).expect("successful allocation");
    /// assert_eq!(instance.capacity_front(), 512);
    ///
    /// // Reserving for wrong end of the buffer, but be empty.
    /// instance.reserve_back(1024).expect("successful allocation");
    /// assert_eq!(instance.capacity_front(), 1024);
    ///
    /// // That many elements can be prepended without invalidating pointers.
    /// let ptr = instance.as_ptr();
    /// for _ in 0..instance.capacity_back() {
    ///     assert!(instance.prepend(12345).is_ok()) // Cannot fail.
    /// }
    /// assert_eq!(instance.as_ptr(), ptr)
    /// ```
    pub fn capacity_front(&self) -> usize {
        if self.initialized == 0 {
            self.pre_capacity + self.post_capacity
        } else {
            self.pre_capacity
        }
    }

    /// How many elements can [`Self::append`] in constant time/without reallocation.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::list::List;
    ///
    /// // Constructing with generic capacity.
    /// let mut instance = Dynamic::<usize>::with_capacity(256).unwrap();
    /// assert_eq!(instance.capacity_back(), 256);
    ///
    /// // Reserving for specific end of the buffer.
    /// instance.reserve_back(512).expect("successful allocation");
    /// assert_eq!(instance.capacity_back(), 512);
    ///
    /// // Reserving for wrong end of the buffer, but be empty.
    /// instance.reserve_front(1024).expect("successful allocation");
    /// assert_eq!(instance.capacity_back(), 1024);
    ///
    /// // That many elements can be appended without invalidating pointers.
    /// let ptr = instance.as_ptr();
    /// for _ in 0..instance.capacity_back() {
    ///     assert!(instance.append(12345).is_ok()) // Cannot fail.
    /// }
    /// assert_eq!(instance.as_ptr(), ptr)
    /// ```
    pub fn capacity_back(&self) -> usize {
        if self.initialized == 0 {
            self.pre_capacity + self.post_capacity
        } else {
            self.post_capacity
        }
    }

    /// Attempt to allocate space for at least `capacity` additional elements.
    ///
    /// In contrast to [`Self::reserve_back`], this method will [`Self::shift`]
    /// the elements to the front of the buffer to create space (thereby making
    /// [`Self::capacity_front`] zero), (re)allocating if necessary to increase
    /// [`Self::capacity_back`].
    ///
    /// This method increases the size of buffer by a geometric progression
    /// with a growth factor of two (2), hence the buffer could ideally contain
    /// a power of two (2) number of elements. This means it may allocate more
    /// memory than explicitly requested, but will attempt to recover when
    /// exactly `capacity` can be allocated, but not more.
    ///
    /// See also: [`Self::reserve_front`] or [`Self::reserve_back`] to reserve
    /// an exact amount of elements at a specific end of the buffer without
    /// [`Self::shift`].
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
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::list::List;
    ///
    /// let mut instance = Dynamic::<usize>::default();
    ///
    /// // From empty instance.
    /// instance.reserve(256).expect("successful allocation");
    ///
    /// // That many elements can be appended without invalidating pointers.
    /// let ptr = instance.as_ptr();
    /// for _ in 0..instance.capacity() {
    ///     assert!(instance.append(12345).is_ok()); // cannot fail.
    /// }
    /// assert_eq!(instance.as_ptr(), ptr);
    ///
    /// // Shifts elements to consume capacity at the front of the buffer.
    /// instance.reserve_front(256).expect("successful allocation");
    /// assert!(instance.reserve(512).is_ok()); // No reallocation, just shift.
    /// for _ in 0..instance.capacity() {
    ///     assert!(instance.append(12345).is_ok()) // Cannot fail.
    /// }
    /// ```
    pub fn reserve(&mut self, capacity: usize) -> Result<&mut Self, FailedAllocation> {
        let total_size = self
            .initialized
            .checked_add(capacity)
            .ok_or(FailedAllocation)?;

        let offset = isize::try_from(self.pre_capacity).expect("cannot exceed isize::MAX");

        if self.initialized > 0 {
            let _ = self.shift(-offset).expect("front capacity to shift into");
        }

        if self.capacity_back() >= capacity {
            // Shifting initialized elements has created enough capacity.
            Ok(self)
        } else {
            // See: https://en.wikipedia.org/wiki/Dynamic_array#Geometric_expansion_and_amortized_cost
            let amortized = total_size.checked_next_power_of_two().unwrap_or(capacity);

            if self.reserve_back(amortized).is_ok() {
                Ok(self)
            } else {
                self.reserve_back(capacity)
            }
        }
    }

    /// Allocate space for exactly `capacity` elements to be prepended.
    ///
    /// # Panics
    /// The Rust runtime might panic or otherwise `abort` if allocation fails.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::list::List;
    ///
    /// let mut instance = Dynamic::<usize>::default();
    ///
    /// // From empty instance.
    /// instance.reserve_front(256).expect("successful allocation");
    ///
    /// // That many elements can be prepended without invalidating pointers.
    /// let ptr = instance.as_ptr();
    /// for _ in 0..instance.capacity() {
    ///     assert!(instance.prepend(12345).is_ok()); // cannot fail.
    /// }
    /// assert_eq!(instance.as_ptr(), ptr);
    /// ```
    pub fn reserve_front(&mut self, capacity: usize) -> Result<&mut Self, FailedAllocation> {
        if self.capacity_front() > capacity {
            return Ok(self);
        }

        let capacity = capacity
            .checked_sub(self.capacity_front())
            .ok_or(FailedAllocation)?;

        // Allocator API ensures total allocation size in bytes will fit into
        // `isize`, so this number of elements allocated will too.
        let capacity = isize::try_from(capacity).unwrap();

        let _ = self.resize(capacity)?;

        if self.initialized > 0 {
            let _ = self.shift(capacity).expect("back capacity to shift into");
        }

        Ok(self)
    }

    /// Allocate space for exactly `capacity` elements to be appended.
    ///
    /// # Panics
    /// The Rust runtime might panic or otherwise `abort` if allocation fails.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    /// use rust::structure::collection::linear::array::Array;
    /// use rust::structure::collection::linear::list::List;
    ///
    /// let mut instance = Dynamic::<usize>::default();
    ///
    /// // From empty instance.
    /// instance.reserve_back(256).expect("successful allocation");
    ///
    /// // That many elements can be prepended without invalidating pointers.
    /// let ptr = instance.as_ptr();
    /// for _ in 0..instance.capacity() {
    ///     assert!(instance.append(12345).is_ok()); // cannot fail.
    /// }
    /// assert_eq!(instance.as_ptr(), ptr);
    /// ```
    pub fn reserve_back(&mut self, capacity: usize) -> Result<&mut Self, FailedAllocation> {
        if self.capacity_back() > capacity {
            return Ok(self);
        }

        let capacity = capacity
            .checked_sub(self.capacity_back())
            .ok_or(FailedAllocation)?;

        if let Ok(capacity) = isize::try_from(capacity) {
            self.resize(capacity)
        } else {
            Err(FailedAllocation)
        }
    }

    /// Attempt to reduce [`Self::capacity`] to exactly `capacity`, or none/zero.
    ///
    /// # Panics
    /// The Rust runtime might panic or otherwise `abort` if allocation fails.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    ///
    /// In contrast to [`Self::shrink_back`], this method will [`Self::shift`]
    /// the elements to the front of the buffer, _always_ shrinking
    /// [`Self::capacity_front`] to zero, reallocating if necessary to decrease
    /// [`Self::capacity_back`].
    ///
    /// See also: [`Self::shrink_front`] or [`Self::shrink_back`] to shrink a
    /// specific end of the buffer without shifting initialized elements.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    /// use rust::structure::collection::linear::list::List;
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
    /// assert_eq!(instance.capacity_back(), 0);
    /// ```
    pub fn shrink(&mut self, capacity: Option<usize>) -> Result<&mut Self, FailedAllocation> {
        // Allocator API ensures total allocation size in bytes will fit into
        // `isize`, so this number of elements allocated will too.
        let offset = isize::try_from(self.capacity_front()).unwrap();

        if self.initialized > 0 {
            let _ = self.shift(-offset).expect("front capacity to shift into");
        } else {
            self.post_capacity += self.pre_capacity;
            self.pre_capacity = 0;
        }

        let capacity = capacity.unwrap_or(0);
        let extra_capacity = self
            .capacity_back()
            .checked_sub(capacity)
            .ok_or(FailedAllocation)?;

        // Allocator API ensures total allocation size in bytes will fit into
        // `isize`, so this number of elements allocated will too.
        let extra_capacity = isize::try_from(extra_capacity).unwrap();

        self.resize(-extra_capacity)
    }

    /// Reallocate to reduce [`Self::capacity_front`] to exactly `capacity`.
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
    /// use rust::structure::collection::linear::list::List;
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
    pub fn shrink_front(&mut self, capacity: Option<usize>) -> Result<&mut Self, FailedAllocation> {
        let capacity = capacity.unwrap_or(0);

        let extra_capacity = self
            .capacity_front()
            .checked_sub(capacity)
            .ok_or(FailedAllocation)?;

        // SAFETY: Allocator API ensures total allocation size in bytes will
        // fit into `isize`, so this number of elements allocated will too.
        let extra_capacity = isize::try_from(extra_capacity).unwrap();

        if self.initialized > 0 {
            let _ = self
                .shift(-extra_capacity)
                .expect("front capacity to shift into");
        }

        self.resize(-extra_capacity)
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
    /// use rust::structure::collection::linear::list::List;
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
    pub fn shrink_back(&mut self, capacity: Option<usize>) -> Result<&mut Self, FailedAllocation> {
        let capacity = capacity.unwrap_or(0);

        let extra_capacity = self
            .capacity_back()
            .checked_sub(capacity)
            .ok_or(FailedAllocation)?;

        // SAFETY: Allocator API ensures total allocation size in bytes will
        // fit into `isize`, so this number of elements allocated will too.
        let extra_capacity = isize::try_from(extra_capacity).unwrap();

        self.resize(-extra_capacity)
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
    /// use rust::structure::collection::linear::list::List;
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
    /// assert_eq!(instance.capacity_back(), 512);
    ///
    /// // Shift initialized elements to the end of the buffer.
    /// instance.shift(512).expect("offset <= capacity_back()");
    /// instance.shift(1).expect_err("offset out of bounds");
    /// assert_eq!(instance.capacity_front(), 512);
    /// assert_eq!(instance.capacity_back(), 0);
    /// ```
    pub fn shift(&mut self, offset: isize) -> Result<&mut Self, OutOfBounds> {
        if self.initialized == 0 {
            return if offset == 0 {
                Ok(self)
            } else {
                Err(OutOfBounds)
            };
        }

        let source = self.as_mut_ptr();

        match offset.cmp(&0) {
            std::cmp::Ordering::Less => {
                if offset.unsigned_abs() > self.pre_capacity || self.pre_capacity == 0 {
                    return Err(OutOfBounds);
                }

                self.pre_capacity -= offset.unsigned_abs();
                self.post_capacity += offset.unsigned_abs();
            }
            std::cmp::Ordering::Greater => {
                if offset.unsigned_abs() > self.post_capacity || self.post_capacity == 0 {
                    return Err(OutOfBounds);
                }

                self.pre_capacity += offset.unsigned_abs();
                self.post_capacity -= offset.unsigned_abs();
            }
            std::cmp::Ordering::Equal => return Ok(self),
        }

        unsafe {
            // SAFETY: aligned within the allocated object.
            let destination = self.as_mut_ptr();

            // SAFETY:
            // * owned memory => source/destination valid for read/writes.
            // * no aliasing restrictions => source and destination can overlap.
            // * underlying buffer is aligned => both pointers are aligned.
            std::ptr::copy(source, destination, self.initialized);
        }

        Ok(self)
    }

    /// Optimally remove elements within `range` by-value.
    ///
    /// This method is more efficient than using `remove` for sequential
    /// elements, moving elements out of the buffer as iterated and shifting
    /// once only when the [`Drain`] has been dropped.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::from_iter([0, 1, 2, 3, 4, 5, 6, 7]);
    ///
    /// instance.drain(8..).expect_err("invalid range");
    ///
    /// let mut drain = instance.drain(..2).expect("valid range");
    /// assert_eq!(drain.next(), Some(0));
    /// assert_eq!(drain.next(), Some(1));
    /// std::mem::drop(drain);
    ///
    /// let mut drain = instance.drain(0..2).expect("valid range");
    /// assert_eq!(drain.next(), Some(2));
    /// assert_eq!(drain.next(), Some(3));
    /// std::mem::drop(drain);
    ///
    /// let mut drain = instance.drain(0..=1).expect("valid range");
    /// assert_eq!(drain.next(), Some(4));
    /// assert_eq!(drain.next(), Some(5));
    /// std::mem::drop(drain);
    ///
    /// let mut drain = instance.drain(0..).expect("valid range");
    /// assert_eq!(drain.next(), Some(6));
    /// assert_eq!(drain.next(), Some(7));
    /// std::mem::drop(drain);
    ///
    /// instance.drain(..).expect_err("invalid range/no elements to drain");
    /// ```
    pub fn drain<R: std::ops::RangeBounds<usize>>(
        &mut self,
        range: R,
    ) -> Result<Drain<'_, T>, OutOfBounds> {
        let start = match range.start_bound() {
            std::ops::Bound::Included(start) => *start,
            std::ops::Bound::Excluded(start) => *start + 1,
            std::ops::Bound::Unbounded => 0,
        };

        let end = match range.end_bound() {
            std::ops::Bound::Included(end) => *end + 1,
            std::ops::Bound::Excluded(end) => *end,
            std::ops::Bound::Unbounded => self.len(),
        };

        if start >= self.len() || end > self.len() {
            return Err(OutOfBounds);
        }

        let range = start..end;

        Ok(Drain {
            underlying: self,
            range: range.clone(),
            next: range.clone(),
        })
    }

    /// Remove the elements which match some `predicate`.
    ///
    /// The `predicate` is called exactly once per each element, in order.
    /// Elements for which the `predicate` is true are removed in order from
    /// left to right. Elements for which the `predicate` is false are shifted
    /// left to immediately after the previously retained element, thereby
    /// maintaining order.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut withdraw = instance.withdraw(|element| element % 2 == 0);
    ///
    /// assert_eq!(withdraw.next(), Some(0));
    /// assert_eq!(withdraw.next_back(), Some(4));
    ///
    /// drop(withdraw);
    ///
    /// assert!(instance.eq([1, 3, 5]));
    /// ```
    pub fn withdraw<F: FnMut(&T) -> bool>(&mut self, predicate: F) -> Withdraw<'_, T, F> {
        let head = if self.initialized == 0 {
            // SAFETY: this pointer will not be modified or read.
            std::ptr::NonNull::dangling()
        } else {
            // SAFETY: at least one element exist => pointer cannot be null.
            unsafe { std::ptr::NonNull::new_unchecked(self.as_mut_ptr()) }
        };

        let tail = if self.initialized == 0 {
            head
        } else {
            // SAFETY: stays aligned within the allocated object.
            unsafe {
                // SAFETY: at least one element exists => cannot underflow.
                let offset = self.initialized - 1;

                // SAFETY: stays aligned within the allocated object.
                let ptr = head.as_ptr().add(offset);

                // SAFETY: `head` cannot be null => pointer cannot be null.
                std::ptr::NonNull::new_unchecked(ptr)
            }
        };

        let remaining = self.initialized;

        Withdraw {
            underlying: self,
            predicate,
            remaining,
            retained: head,
            head,
            tail,
            trailing: 0,
        }
    }

    /// Drop elements which don't match some `predicate`.
    ///
    /// Same as [`Self::withdraw`] all elements that do not match `predicate`.
    ///
    /// # Performance
    /// This method takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// instance.retain(|element| element % 2 == 0);
    ///
    /// assert!(instance.eq([0, 2, 4]));
    /// ```
    pub fn retain<F: FnMut(&T) -> bool>(&mut self, mut predicate: F) {
        self.withdraw(|element| !predicate(element)).for_each(drop)
    }

    /// Remove an element by swapping it with the first element.
    ///
    /// In contrast to [`Self::remove`], this method takes constant time and
    /// does _NOT_ preserve order.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(instance.remove_via_front(3), Some(3));
    /// assert_eq!(instance.capacity_front(), 1);
    /// assert_eq!(instance[2], 0);
    /// ```
    pub fn remove_via_front(&mut self, index: usize) -> Option<T> {
        if index >= self.initialized {
            None
        } else {
            let element: T;

            unsafe {
                let front = self.as_mut_ptr();

                // SAFETY: index is in bounds => aligned within the allocated object.
                let index = front.add(index);

                // SAFETY:
                // * both pointers are valid for reads and write.
                // * both pointers are aligned.
                // * no aliasing restrictions.
                std::ptr::swap(front, index);

                // SAFETY: this takes ownership (moved out of buffer).
                element = front.read();
            }

            self.initialized -= 1;
            self.pre_capacity += 1;

            Some(element)
        }
    }

    /// Remove an element by swapping it with the last element.
    ///
    /// In contrast to [`Self::remove`], this method takes constant time and
    /// does _NOT_ preserve order.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(instance.remove_via_back(3), Some(3));
    /// assert_eq!(instance.capacity_back(), 1);
    /// assert_eq!(instance[3], 5);
    /// ```
    pub fn remove_via_back(&mut self, index: usize) -> Option<T> {
        if index >= self.initialized {
            None
        } else {
            let element: T;

            unsafe {
                let ptr = self.as_mut_ptr();

                // SAFETY: at least one element => aligned within the allocated object.
                let last = ptr.add(self.initialized - 1);

                // SAFETY: index is in bounds => aligned within the allocated object.
                let index = ptr.add(index);

                // SAFETY:
                // * both pointers are valid for reads and write.
                // * both pointers are aligned.
                // * no aliasing restrictions.
                std::ptr::swap(last, index);

                // SAFETY: this takes ownership (moved out of buffer).
                element = last.read()
            }

            self.post_capacity += 1;
            self.initialized -= 1;

            Some(element)
        }
    }

    /// (Re)allocate the buffer to modify [`capacity_back`] by `capacity`.
    ///
    /// This method will increase [`capacity_back`] by `capacity` if positive,
    /// and decrease by `capacity` if negative, (re)allocating if necessary.
    ///
    /// Note that failed allocation will _NOT_ modify the underlying buffer.
    ///
    /// # Panics
    /// The Rust runtime might panic or otherwise `abort` if allocation fails.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    fn resize(&mut self, capacity: isize) -> Result<&mut Self, FailedAllocation> {
        // Treat all capacity as back capacity when empty.
        if self.initialized == 0 {
            self.post_capacity += self.pre_capacity;
            self.pre_capacity = 0;
        }

        let capacity = self
            .post_capacity
            .checked_add_signed(capacity)
            .ok_or(FailedAllocation)?;

        // Zero-size types do _NOT_ occupy memory, so no (re/de)allocation.
        if std::mem::size_of::<T>() == 0 {
            self.post_capacity = capacity;

            return Ok(self);
        }

        // SAFETY: Allocator API ensures total allocation size in bytes will
        // fit into `isize`, so these number of elements allocated will too.
        let front = self.pre_capacity + self.initialized;
        let total = front + self.post_capacity;

        let new_layout = {
            let total = front.checked_add(capacity).ok_or(FailedAllocation)?;

            match std::alloc::Layout::array::<T>(total) {
                Ok(layout) => layout,
                Err(_) => return Err(FailedAllocation),
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
                    Err(_) => return Err(FailedAllocation),
                };

                unsafe {
                    let ptr = self.buffer.as_ptr().cast::<u8>();

                    // Deallocate.
                    if front == 0 && capacity == 0 {
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
            None => return Err(FailedAllocation),
        };

        self.post_capacity = capacity;

        Ok(self)
    }
}

impl<T> Drop for Dynamic<T> {
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

        let _ = self.resize(0).expect("deallocation cannot fail");
    }
}

impl<'a, T: 'a + Clone> TryFrom<&'a [T]> for Dynamic<T> {
    type Error = FailedAllocation;

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

        instance.extend(slice.iter().cloned());

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

impl<T> Iterator for Dynamic<T> {
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

impl<T> DoubleEndedIterator for Dynamic<T> {
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

impl<T> ExactSizeIterator for Dynamic<T> {}

impl<T> std::iter::FusedIterator for Dynamic<T> {}

impl<'a, T: 'a> FromIterator<T> for Dynamic<T> {
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

impl<T> Extend<T> for Dynamic<T> {
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
        let iter = iter.into_iter();

        // SAFETY: `size_hint` can _NOT_ be trusted to exact size.
        let count = {
            let (min, max) = iter.size_hint();
            max.unwrap_or(min)
        };

        // It is okay if this fails, lazy allocate for each individual element.
        let _ = self.reserve_back(count);

        for element in iter {
            if self.append(element).is_err() {
                panic!("allocation failed, could not append element");
            }
        }
    }
}

impl<T> Default for Dynamic<T> {
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

impl<T: PartialEq> PartialEq for Dynamic<T> {
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

impl<T: Eq> Eq for Dynamic<T> {}

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
        std::fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}

impl<'a, T: 'a> Collection<'a> for Dynamic<T> {
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
    ) -> impl DoubleEndedIterator<Item = &'a Self::Element> + ExactSizeIterator + std::iter::FusedIterator
    {
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
    ) -> impl DoubleEndedIterator<Item = &'a mut Self::Element>
           + ExactSizeIterator
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
    fn as_ptr(&self) -> *const Self::Element {
        // If no allocation then the pointer is dangling and meaningless.
        assert!(self.pre_capacity + self.initialized + self.post_capacity > 0);

        // SAFETY: `MaybeUninit<T>` has the same layout as `T`.
        let ptr = self.buffer.cast::<T>().as_ptr().cast_const();

        // SAFETY: Stays aligned within the allocated object.
        unsafe { ptr.add(self.pre_capacity) }
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
    fn as_mut_ptr(&mut self) -> *mut Self::Element {
        // If no allocation then the pointer is dangling and meaningless.
        assert!(self.pre_capacity + self.initialized + self.post_capacity > 0);

        // SAFETY: `MaybeUninit<T>` has the same layout as `T`.
        let ptr = self.buffer.cast::<T>().as_ptr();

        // SAFETY: Stays aligned within the allocated object.
        unsafe { ptr.add(self.pre_capacity) }
    }
}

impl<'a, T: 'a> List<'a> for Dynamic<T> {
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

        if index == 0 && self.capacity_front() != 0 {
            if self.initialized == 0 {
                self.pre_capacity += self.post_capacity;
                self.post_capacity = 0;
            }

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
            // SAFETY: index within bounds => aligned within allocated object.
            let ptr = self.as_ptr().add(index);

            // SAFETY:
            // * owned memory => `ptr` is valid for reads.
            // * Underlying `T` is initialized.
            // * This takes ownership.
            ptr.read()
        };

        if index == 0 {
            self.pre_capacity += 1;
        } else {
            unsafe {
                // SAFETY: index within bounds => aligned within allocated object.
                let destination = self.as_mut_ptr().add(index);

                // SAFETY: aligned within the allocated object.
                let source = destination.add(1);

                // SAFETY:
                // * owned memory => source/destination valid for read/writes.
                // * no aliasing restrictions => source and destination can overlap.
                // * underlying buffer is aligned => both pointers are aligned.
                std::ptr::copy(source, destination, self.initialized - index - 1);
            }

            self.post_capacity += 1;
        }

        self.initialized -= 1;

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
    /// assert_eq!(instance.len(), 0);
    /// assert_eq!(instance.capacity(), 6);
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

        self.post_capacity += self.initialized;
        self.initialized = 0;
    }
}

/// By-value [`Iterator`] to remove elements from a [`Dynamic`].
///
/// See [`Dynamic::drain`].
pub struct Drain<'a, T> {
    /// The underlying [`Dynamic`] being drained from.
    underlying: &'a mut Dynamic<T>,

    /// The index range of elements being drained.
    range: std::ops::Range<usize>,

    /// The index range of elements being drained that have yet to be yielded.
    next: std::ops::Range<usize>,
}

impl<T> Drop for Drain<'_, T> {
    /// Drops remaining elements and fixes the underlying [`Dynamic`] buffer.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    /// use rust::structure::collection::linear::Linear;
    ///
    /// let mut instance = Dynamic::from_iter([0, 1, 2, 3, 4, 5, 6]);
    ///
    /// let mut drain = instance.drain(2..=4).expect("valid range");
    ///
    /// drain.next();      // Consumes the element with value `2`.
    /// drain.next_back(); // Consumes the element with value `4`.
    ///
    /// std::mem::drop(drain); // Drops the element with value '3'.
    ///
    /// assert!(instance.into_iter().eq([0, 1, 5, 6])); // Remaining elements.
    /// ```
    fn drop(&mut self) {
        for index in self.next.clone() {
            unsafe {
                let ptr = self.underlying.buffer.as_ptr();

                // SAFETY: stays aligned within the allocated object.
                let ptr = ptr.add(self.underlying.pre_capacity);

                // SAFETY: stays aligned within the allocated object.
                let ptr = ptr.add(index);

                // SAFETY:
                // * The `MaybeUninit<T>` is initialized => safe deref.
                // * The `T` is initialized => safe drop.
                (*ptr).assume_init_drop();
            }
        }

        if self.range.end == self.underlying.initialized {
            self.underlying.post_capacity += self.range.len();
        } else if self.range.start == 0 {
            self.underlying.pre_capacity += self.range.len();
        } else {
            let leading = self.range.start;
            let trailing = self.underlying.initialized - self.range.end;

            let only_front_capacity =
                self.underlying.pre_capacity != 0 && self.underlying.post_capacity == 0;
            let only_back_capacity =
                self.underlying.pre_capacity == 0 && self.underlying.post_capacity != 0;

            unsafe {
                let ptr = self.underlying.as_mut_ptr();

                let source: *mut T;
                let destination: *mut T;
                let count: usize;

                if only_front_capacity || (!only_back_capacity && trailing > leading) {
                    // [pre_capacity] [remain] [drained] [shift] [post_capacity]

                    self.underlying.post_capacity = self.range.len();

                    count = trailing;

                    // SAFETY: stays aligned within the allocated object.
                    source = ptr.add(self.range.end);

                    // SAFETY: stays aligned within the allocated object.
                    destination = ptr.add(self.range.start);
                } else {
                    // [pre_capacity] [shift] [drained] [remain] [post_capacity]

                    self.underlying.pre_capacity = self.range.len();

                    count = leading;

                    source = ptr;

                    // SAFETY: stays aligned within the allocated object.
                    destination = ptr.add(self.range.len());
                }

                // SAFETY:
                // * owned memory => source/destination valid for read/writes.
                // * no aliasing restrictions => source and destination can overlap.
                // * underlying buffer is aligned => both pointers are aligned.
                std::ptr::copy(source, destination, count);
            }
        }

        self.underlying.initialized -= self.range.len();
    }
}

impl<T> Iterator for Drain<'_, T> {
    type Item = T;

    /// Obtain the next element, if there are any left.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut underlying = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut actual = underlying.drain(..).expect("valid range");
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
        let ptr = self.underlying.buffer.as_ptr();

        // SAFETY: stays aligned within the allocated object.
        let ptr = unsafe { ptr.add(self.underlying.pre_capacity) };

        if let Some(index) = self.next.next() {
            // SAFETY: stays aligned within the allocated object.
            let ptr = unsafe { ptr.add(index) };

            // SAFETY:
            // * `ptr` is valid => safe to dereference.
            // * underlying `T` is initialized.
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
    /// let mut underlying = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut actual = underlying.drain(..).expect("valid range");
    ///
    /// assert_eq!(actual.size_hint(), (6, Some(6)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.next.len(), Some(self.next.len()))
    }
}

impl<T> DoubleEndedIterator for Drain<'_, T> {
    /// Obtain the final element, if there are any left.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut underlying = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut actual = underlying.drain(..).expect("valid range");
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
        let ptr = self.underlying.buffer.as_ptr();

        // SAFETY: stays aligned within the allocated object.
        let ptr = unsafe { ptr.add(self.underlying.pre_capacity) };

        if let Some(index) = self.next.next_back() {
            // SAFETY: stays aligned within the allocated object.
            let ptr = unsafe { ptr.add(index) };

            // SAFETY:
            // * `ptr` is valid => safe to dereference.
            // * underlying `T` is initialized.
            Some(unsafe { (*ptr).assume_init_read() })
        } else {
            None
        }
    }
}

impl<T> ExactSizeIterator for Drain<'_, T> {}

impl<T> std::iter::FusedIterator for Drain<'_, T> {}

impl<T: std::fmt::Debug> std::fmt::Debug for Drain<'_, T> {
    /// List the elements being drained.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut underlying = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    /// let actual = underlying.drain(1..4);
    ///
    /// assert_eq!(format!("{actual:?}"), format!("Ok([1, 2, 3])"));
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let ptr = self.underlying.as_ptr();

        let mut list = f.debug_list();

        for index in self.next.clone() {
            let _ = list.entry(unsafe { &*ptr.add(index) });
        }

        list.finish()
    }
}

/// By-value [`Iterator`] to remove elements from a [`Dynamic`].
///
/// See [`Dynamic::withdraw`].
pub struct Withdraw<'a, T, F: FnMut(&T) -> bool> {
    /// The underlying [`Dynamic`] begin withdrawn from.
    underlying: &'a mut Dynamic<T>,

    /// The predicate based upon which elements are withdrawn.
    predicate: F,

    /// Where to write the next retained element to.
    retained: std::ptr::NonNull<T>,

    /// How many element are left to query with the predicate.
    remaining: usize,

    /// The next (front) element to query with the predicate.
    head: std::ptr::NonNull<T>,

    /// The next (back) element to query with the predicate.
    tail: std::ptr::NonNull<T>,

    /// The number of retained elements at the end because of `next_back`.
    trailing: usize,
}

impl<T, F: FnMut(&T) -> bool> Drop for Withdraw<'_, T, F> {
    /// Drops remaining elements and fixes the underlying [`Dynamic`] buffer.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    ///
    /// let mut withdraw = instance.withdraw(|element| element % 2 == 0);
    ///
    /// assert_eq!(withdraw.next(), Some(0));      // Consumes the element with value `0`.
    /// assert_eq!(withdraw.next_back(), Some(4)); // Consumes the element with value `4`.
    ///
    /// drop(withdraw); // Drops the element with value '2'.
    ///
    /// assert!(instance.eq([1, 3, 5])); // Retained elements.
    /// ```
    fn drop(&mut self) {
        // Drop all remaining elements to withdraw.
        self.for_each(drop);

        // Shift any string of trailing retained elements into position.
        unsafe {
            // SAFETY: aligned within the allocated object, or one byte past.
            let trailing = self.tail.as_ptr().add(1);

            // SAFETY:
            // * owned memory => source/destination valid for read/writes.
            // * no aliasing restrictions => source and destination can overlap.
            // * underlying buffer is aligned => both pointers are aligned.
            std::ptr::copy(trailing, self.retained.as_ptr(), self.trailing)
        };
    }
}

impl<T, F: FnMut(&T) -> bool> Iterator for Withdraw<'_, T, F> {
    type Item = T;

    /// Obtain the next element, if there are any left.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut underlying = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut actual = underlying.withdraw(|element| element % 2 == 0);
    ///
    /// assert_eq!(actual.next(), Some(0));
    /// assert_eq!(actual.next(), Some(2));
    /// assert_eq!(actual.next(), Some(4));
    /// assert_eq!(actual.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        let first_retained = self.head;
        let mut consecutive_retained = 0;

        // Shift the current run of retained elements to the left.
        let shift_retained = |src: *mut T, dst: *mut T, count| unsafe {
            // SAFETY:
            // * owned memory => source/destination valid for read/writes.
            // * no aliasing restrictions => source and destination can overlap.
            // * underlying buffer is aligned => both pointers are aligned.
            std::ptr::copy(src, dst, count);
        };

        while self.remaining != 0 {
            self.remaining -= 1;

            // SAFETY: the element is initialized.
            let current = unsafe { self.head.as_ref() };

            self.head = unsafe {
                // SAFETY: aligned within the allocated object, or one byte past.
                let ptr = self.head.as_ptr().add(1);

                // SAFETY: `head` is not null => pointer is not null.
                std::ptr::NonNull::new_unchecked(ptr)
            };

            if (self.predicate)(current) {
                // SAFETY: this takes ownership (moved out of buffer).
                let element = unsafe { std::ptr::read(current) };

                // Increase pre-capacity rather than shift into it when the
                // first element is being withdrawn, this ensures the first
                // retained element does not move.
                if self.underlying.as_ptr() == current {
                    self.underlying.pre_capacity += 1;

                    self.retained = unsafe {
                        // SAFETY: aligned within the allocated object, or one byte past.
                        let ptr = self.retained.as_ptr().add(1);

                        // SAFETY: `retained` is not null => pointer is not null.
                        std::ptr::NonNull::new_unchecked(ptr)
                    };
                } else {
                    self.underlying.post_capacity += 1;
                }

                shift_retained(
                    first_retained.as_ptr(),
                    self.retained.as_ptr(),
                    consecutive_retained,
                );

                self.retained = unsafe {
                    // SAFETY: aligned within the allocated object, or one byte past.
                    let ptr = self.retained.as_ptr().add(consecutive_retained);

                    // SAFETY: `retained` is not null => pointer is not null.
                    std::ptr::NonNull::new_unchecked(ptr)
                };

                self.underlying.initialized -= 1;

                return Some(element);
            } else {
                consecutive_retained += 1;
            }
        }

        // The above loop will exit whenever there are no more remaining
        // elements to query with the predicate. However, this means the loop
        // may iterate through a string of elements to retain at the end of the
        // buffer before exhausting elements to query. In such a circumstance,
        // there is no element at the end to withdraw hence the loop will exit
        // without shifting these elements to align with previously retained
        // elements. Nevertheless, previous iterations of the loop ensure the
        // pointer and counter denote a valid range of retained elements (if
        // any) so they can still be shifted before returning none.
        shift_retained(
            first_retained.as_ptr(),
            self.retained.as_ptr(),
            consecutive_retained,
        );

        self.retained = unsafe {
            // SAFETY: aligned within the allocated object, or one byte past.
            let ptr = self.retained.as_ptr().add(consecutive_retained);

            // SAFETY: `retained` is not null => pointer is not null.
            std::ptr::NonNull::new_unchecked(ptr)
        };

        None
    }

    /// Query how many elements can be yielded.
    ///
    /// # Performance
    /// This method takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut underlying = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    /// let instance = underlying.withdraw(|element| element % 2 == 0);
    ///
    /// assert_eq!(instance.size_hint(), (0, Some(6)));
    /// ```
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.remaining))
    }
}

impl<T, F: FnMut(&T) -> bool> DoubleEndedIterator for Withdraw<'_, T, F> {
    /// Obtain the next element, if there are any left.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut underlying = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut actual = underlying.withdraw(|element| element % 2 == 0);
    ///
    /// assert_eq!(actual.next_back(), Some(4));
    /// assert_eq!(actual.next_back(), Some(2));
    /// assert_eq!(actual.next_back(), Some(0));
    /// assert_eq!(actual.next_back(), None);
    /// ```
    fn next_back(&mut self) -> Option<Self::Item> {
        while self.remaining != 0 {
            self.remaining -= 1;

            // SAFETY: the element is initialized.
            let current = unsafe { self.tail.as_ref() };

            unsafe {
                // SAFETY: prevent moving the pointer to before the allocated object.
                if self.remaining != 0 {
                    self.tail = {
                        // SAFETY: aligned within the allocated object.
                        let ptr = self.tail.as_ptr().sub(1);

                        // SAFETY: `retained` is not null => pointer is not null.
                        std::ptr::NonNull::new_unchecked(ptr)
                    };
                }
            }

            if (self.predicate)(current) {
                // SAFETY: this takes ownership (moved out of buffer).
                let element = unsafe { std::ptr::read(current) };

                self.underlying.initialized -= 1;
                self.underlying.post_capacity += 1;

                let src = {
                    let current: *const T = current;

                    // SAFETY: stays aligned within the allocated object.
                    unsafe { current.add(1) }.cast_mut()
                };

                let dst = {
                    let current: *const T = current;
                    current.cast_mut()
                };

                // SAFETY:
                // * owned memory => source/destination valid for read/writes.
                // * no aliasing restrictions => source and destination can overlap.
                // * underlying buffer is aligned => both pointers are aligned.
                unsafe { std::ptr::copy(src, dst, self.trailing) };

                return Some(element);
            } else {
                self.trailing += 1;
            }
        }

        None
    }
}

impl<T, F: FnMut(&T) -> bool> std::iter::FusedIterator for Withdraw<'_, T, F> {}

impl<T, F: FnMut(&T) -> bool> std::fmt::Debug for Withdraw<'_, T, F> {
    /// Output what indexes are being pointed to in the underlying buffer.
    ///
    /// Note that these indexes are _NOT_ based on the first initialized
    /// element, but rather absolute relative to the beginning of the
    /// allocated object.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut underlying = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
    /// let mut withdraw = underlying.withdraw(|element| element % 2 == 0);
    ///
    /// println!("{withdraw:?}")
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let origin = self.underlying.buffer.as_ptr().cast::<T>();

        // SAFETY: both pointers are aligned within the allocated object.
        let head = unsafe { self.head.as_ptr().offset_from(origin) };

        // SAFETY: both pointers are aligned within the allocated object.
        let retained = unsafe { self.retained.as_ptr().offset_from(origin) };

        // SAFETY: both pointers are aligned within the allocated object.
        let tail = unsafe { self.tail.as_ptr().offset_from(origin) };

        f.debug_struct("Withdraw")
            .field("head index", &head)
            .field("tail index", &tail)
            .field("remaining elements", &self.remaining)
            .field("retained index", &retained)
            .field("trailing elements", &self.trailing)
            .finish_non_exhaustive()
    }
}

/// Error type for recoverable allocation failure.
#[derive(Debug, Clone, Copy)]
pub struct FailedAllocation;

impl std::fmt::Display for FailedAllocation {
    /// Write a human-facing description of the error.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "memory allocation failed")
    }
}

impl std::error::Error for FailedAllocation {}

/// Error type for invalid index parameters.
#[derive(Debug, Clone, Copy)]
pub struct OutOfBounds;

impl std::fmt::Display for OutOfBounds {
    /// Write a human-facing description of the error.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "index is outside the bounds of initialized elements")
    }
}

impl std::error::Error for OutOfBounds {}

#[cfg(test)]
mod test {
    use super::*;

    mod method {
        use super::*;

        mod with_capacity {
            use super::*;

            #[test]
            fn increases_capacity() {
                let actual = Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                assert_eq!(actual.capacity(), 256);
                assert_eq!(actual.capacity_front(), 256);
                assert_eq!(actual.capacity_back(), 256);
            }

            #[test]
            fn allocates_memory() {
                let actual = Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                for index in 0..actual.capacity() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn does_not_initialize_elements() {
                let actual = Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                assert_eq!(actual.initialized, 0);
            }

            #[test]
            fn zero_capacity_cannot_fail() {
                let actual = Dynamic::<usize>::with_capacity(0);

                assert!(actual.is_ok());
            }

            #[test]
            fn zero_size_types_cannot_fail() {
                let capacity = usize::try_from(isize::MAX).unwrap();

                let actual = Dynamic::<()>::with_capacity(capacity);

                assert!(actual.is_ok());
            }
        }

        mod capacity {
            use super::*;

            #[test]
            fn only_front_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_front(256).expect("successful allocation");

                assert_eq!(actual.capacity(), 256);
            }

            #[test]
            fn only_back_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_back(256).expect("successful allocation");

                assert_eq!(actual.capacity(), 256);
            }

            #[test]
            fn front_and_back_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_front(256).expect("successful allocation");
                let _ = actual.reserve_back(256).expect("successful allocation");

                assert_eq!(actual.capacity(), 512);
            }

            #[test]
            fn does_not_invalidate_pointers_for_that_many_additions() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let ptr = actual.buffer.as_ptr();

                for index in 0..actual.capacity() {
                    if index % 2 == 0 {
                        let _ = actual.append(index).expect("uses capacity");
                    } else {
                        let _ = actual.prepend(index).expect("uses capacity");
                    }
                }

                assert_eq!(ptr, actual.buffer.as_ptr());
            }
        }

        mod capacity_front {
            use super::*;

            #[test]
            fn is_pre_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_front(256).expect("successful allocation");

                assert_eq!(actual.capacity_front(), actual.pre_capacity);
            }

            #[test]
            fn does_not_count_back_capacity_when_not_empty() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_back(256).expect("successful allocation");

                assert_eq!(actual.capacity_front(), 0);
            }

            #[test]
            fn counts_back_capacity_when_empty() {
                let mut actual = Dynamic::<usize>::default();

                let _ = actual.reserve_back(256).expect("successful allocation");

                assert_eq!(actual.capacity_front(), 256);
            }

            #[test]
            fn does_not_invalidate_pointers_for_that_many_prepends() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let ptr = actual.buffer.as_ptr();

                for index in 0..actual.capacity_front() {
                    let _ = actual.prepend(index).expect("uses capacity");
                }

                assert_eq!(ptr, actual.buffer.as_ptr());
            }
        }

        mod capacity_back {
            use super::*;

            #[test]
            fn is_post_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_back(256).expect("successful allocation");

                assert_eq!(actual.capacity_back(), actual.post_capacity);
            }

            #[test]
            fn does_not_count_front_capacity_when_not_empty() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_front(256).expect("successful allocation");

                assert_eq!(actual.capacity_back(), 0);
            }

            #[test]
            fn counts_front_capacity_when_empty() {
                let mut actual = Dynamic::<usize>::default();

                let _ = actual.reserve_front(256).expect("successful allocation");

                assert_eq!(actual.capacity_back(), 256);
            }

            #[test]
            fn does_not_invalidate_pointers_for_that_many_appends() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let ptr = actual.buffer.as_ptr();

                for index in 0..actual.capacity_back() {
                    let _ = actual.append(index).expect("uses capacity");
                }

                assert_eq!(ptr, actual.buffer.as_ptr());
            }
        }

        mod reserve {
            use super::*;

            #[test]
            fn increases_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve(1).expect("successful allocation");

                assert!(actual.capacity() >= 1);
            }

            #[test]
            fn increases_capacity_in_powers_of_two() {
                let mut actual = Dynamic::<()>::default();

                for _ in 0..(isize::BITS) {
                    let capacity = actual.capacity() + 1;

                    let _ = actual.reserve(capacity).expect("successful allocation");

                    let capacity = capacity.checked_next_power_of_two().unwrap();

                    assert_eq!(actual.capacity(), capacity);
                }
            }

            #[test]
            fn does_not_decrease_capacity() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                assert!(actual.reserve(0).is_ok());
                assert_eq!(actual.capacity(), 256);
            }

            #[test]
            fn uses_front_capacity_before_reallocating() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_front(256).expect("successful allocation");

                let existing_allocation = actual.buffer.as_ptr();

                assert!(actual.reserve(256).is_ok());

                assert_eq!(actual.buffer.as_ptr(), existing_allocation);
            }

            #[test]
            fn allocates_memory() {
                let mut actual = Dynamic::<usize>::default();

                let _ = actual.reserve(256).expect("successful allocation");

                for index in 0..actual.capacity() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn reallocates_memory() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let _ = actual
                    .reserve(actual.capacity() * 2)
                    .expect("successful allocation");

                for index in 0..actual.capacity() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn does_not_initialize_elements() {
                let mut actual = Dynamic::<usize>::default();

                let _ = actual.reserve(256).expect("successful allocation");

                assert_eq!(actual.initialized, 0);
            }

            #[test]
            fn does_not_modify_initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual = Dynamic::<usize>::from_iter(expected.iter().copied());

                let _ = actual.reserve(256).expect("successful allocation");

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn zero_capacity_cannot_fail() {
                let mut actual = Dynamic::<usize>::default();

                assert!(actual.reserve(0).is_ok());
            }

            #[test]
            fn zero_size_types_cannot_fail() {
                let capacity = usize::try_from(isize::MAX).unwrap();

                let mut actual = Dynamic::<()>::default();

                assert!(actual.reserve(capacity).is_ok());
            }
        }

        mod reserve_front {
            use super::*;

            #[test]
            fn increases_front_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_front(256).expect("successful allocation");

                assert_eq!(actual.capacity_front(), 256);
            }

            #[test]
            fn does_not_decrease_capacity() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                assert!(actual.reserve_front(0).is_ok());
                assert_eq!(actual.capacity_front(), 256);
            }

            #[test]
            fn does_not_modify_back_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_back(256).expect("successful allocation");

                let _ = actual.reserve_front(256).expect("successful allocation");

                assert_eq!(actual.capacity_back(), 256);
            }

            #[test]
            fn allocates_memory() {
                let mut actual = Dynamic::<usize>::default();

                let _ = actual.reserve_front(256).expect("successful allocation");

                for index in 0..actual.capacity_front() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn reallocates_memory() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let _ = actual
                    .reserve_front(actual.capacity_front() * 2)
                    .expect("successful allocation");

                for index in 0..actual.capacity_front() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn does_not_initialize_elements() {
                let mut actual = Dynamic::<usize>::default();

                let _ = actual.reserve_front(256).expect("successful allocation");

                assert_eq!(actual.initialized, 0);
            }

            #[test]
            fn does_not_modify_initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual = Dynamic::from_iter(expected.iter().copied());

                let _ = actual.reserve_front(256).expect("successful allocation");

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn zero_capacity_cannot_fail() {
                let mut actual = Dynamic::<usize>::default();

                assert!(actual.reserve_front(0).is_ok());
            }

            #[test]
            fn zero_size_types_cannot_fail() {
                let capacity = usize::try_from(isize::MAX).unwrap();

                let mut actual = Dynamic::<()>::default();

                assert!(actual.reserve_front(capacity).is_ok());
            }
        }

        mod reserve_back {
            use super::*;

            #[test]
            fn increases_back_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_back(256).expect("successful allocation");

                assert_eq!(actual.capacity_back(), 256);
            }

            #[test]
            fn does_not_decrease_capacity() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                assert!(actual.reserve_back(0).is_ok());
                assert_eq!(actual.capacity_back(), 256);
            }

            #[test]
            fn does_not_modify_front_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_front(256).expect("successful allocation");

                let _ = actual.reserve_back(256).expect("successful allocation");

                assert_eq!(actual.capacity_front(), 256);
            }

            #[test]
            fn allocates_memory() {
                let mut actual = Dynamic::<usize>::default();

                let _ = actual.reserve_back(256).expect("successful allocation");

                for index in 0..actual.capacity_back() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn reallocates_memory() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let _ = actual
                    .reserve_back(actual.capacity_back() * 2)
                    .expect("successful allocation");

                for index in 0..actual.capacity_back() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn does_not_initialize_elements() {
                let mut actual = Dynamic::<usize>::default();

                let _ = actual.reserve_back(256).expect("successful allocation");

                assert_eq!(actual.initialized, 0);
            }

            #[test]
            fn does_not_modify_initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual = Dynamic::from_iter(expected.iter().copied());

                let _ = actual.reserve_back(256).expect("successful allocation");

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn zero_capacity_cannot_fail() {
                let mut actual = Dynamic::<usize>::default();

                assert!(actual.reserve_back(0).is_ok());
            }

            #[test]
            fn zero_size_types_cannot_fail() {
                let capacity = usize::try_from(isize::MAX).unwrap();

                let mut actual = Dynamic::<()>::default();

                assert!(actual.reserve_back(capacity).is_ok());
            }
        }

        mod shrink {
            use super::*;

            #[test]
            fn decreases_capacity_when_some() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let _ = actual.shrink(Some(64)).expect("successful reallocation");

                assert_eq!(actual.capacity(), 64);
            }

            #[test]
            fn removes_capacity_when_none() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let _ = actual.shrink(None).expect("successful reallocation");

                assert_eq!(actual.capacity(), 0);
            }

            #[test]
            fn does_not_increase_capacity() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(64).expect("successful allocation");

                assert!(actual.shrink(Some(256)).is_err());
            }

            #[test]
            fn shrinks_front_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_front(256).expect("successful allocation");

                let _ = actual.shrink(None).expect("successful reallocation");

                assert_eq!(actual.capacity_front(), 0);
            }

            #[test]
            fn shrinks_back_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_back(256).expect("successful allocation");

                let _ = actual.shrink(None).expect("successful reallocation");

                assert_eq!(actual.capacity_back(), 0);
            }

            #[test]
            fn shrinks_front_and_back_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_front(256).expect("successful allocation");
                let _ = actual.reserve_back(256).expect("successful allocation");

                let _ = actual.shrink(None).expect("successful reallocation");

                assert_eq!(actual.capacity_front(), 0);
                assert_eq!(actual.capacity_back(), 0);
            }

            #[test]
            fn reallocates_memory() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let _ = actual.shrink(Some(128)).expect("successful allocation");

                for index in 0..actual.capacity() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn does_not_initialize_elements() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let _ = actual.shrink(Some(128)).expect("successful reallocation");

                assert_eq!(actual.initialized, 0);
            }

            #[test]
            fn does_not_modify_initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                let _ = actual.shrink(None).expect("successful reallocation");

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn zero_capacity_cannot_fail() {
                let mut actual = Dynamic::<usize>::default();

                assert!(actual.shrink(None).is_ok());
            }

            #[test]
            fn zero_size_types_cannot_fail() {
                let mut actual = Dynamic::<()>::with_capacity(256).expect("successful allocation");

                assert!(actual.shrink(None).is_ok());
            }
        }

        mod shrink_front {
            use super::*;

            #[test]
            fn decreases_front_capacity_when_some() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_front(256).expect("successful reallocation");

                let _ = actual
                    .shrink_front(Some(64))
                    .expect("successful reallocation");

                assert_eq!(actual.capacity_front(), 64);
            }

            #[test]
            fn removes_front_capacity_when_none() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_front(256).expect("successful reallocation");

                let _ = actual.shrink_front(None).expect("successful reallocation");

                assert_eq!(actual.capacity_front(), 0);
            }

            #[test]
            fn does_not_increase_capacity() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(64).expect("successful allocation");

                assert!(actual.shrink_front(Some(256)).is_err());
            }

            #[test]
            fn does_not_decrease_back_capacity_when_not_empty() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_back(256).expect("successful allocation");

                let _ = actual.shrink_front(None).expect("no-op");

                assert_eq!(actual.capacity_back(), 256);
            }

            #[test]
            fn decreases_back_capacity_when_empty() {
                let mut actual = Dynamic::<usize>::default();

                let _ = actual.reserve_back(256).expect("successful allocation");

                let _ = actual.shrink_front(None).expect("successful deallocation");

                assert_eq!(actual.capacity_back(), 0);
            }

            #[test]
            fn reallocates_memory() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let _ = actual
                    .shrink_front(Some(128))
                    .expect("successful allocation");

                for index in 0..actual.capacity_front() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn does_not_initialize_elements() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let _ = actual
                    .shrink_front(Some(128))
                    .expect("successful reallocation");

                assert_eq!(actual.initialized, 0);
            }

            #[test]
            fn does_not_modify_initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                let _ = actual.shrink_front(None).expect("successful reallocation");

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn zero_capacity_cannot_fail() {
                let mut actual = Dynamic::<usize>::default();

                assert!(actual.shrink_front(None).is_ok());
            }

            #[test]
            fn zero_size_types_cannot_fail() {
                let mut actual = Dynamic::<()>::with_capacity(256).expect("successful allocation");

                assert!(actual.shrink_front(None).is_ok());
            }
        }

        mod shrink_back {
            use super::*;

            #[test]
            fn decreases_back_capacity_when_some() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_back(256).expect("successful reallocation");

                let _ = actual
                    .shrink_back(Some(64))
                    .expect("successful reallocation");

                assert_eq!(actual.capacity_back(), 64);
            }

            #[test]
            fn removes_back_capacity_when_none() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_back(256).expect("successful reallocation");

                let _ = actual.shrink_back(None).expect("successful reallocation");

                assert_eq!(actual.capacity_back(), 0);
            }

            #[test]
            fn does_not_increase_capacity() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(64).expect("successful allocation");

                assert!(actual.shrink_back(Some(256)).is_err());
            }

            #[test]
            fn does_not_decrease_front_capacity_when_not_empty() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_front(256).expect("successful allocation");

                let _ = actual.shrink_back(None).expect("no-op");

                assert_eq!(actual.capacity_front(), 256);
            }

            #[test]
            fn decreases_front_capacity_when_empty() {
                let mut actual = Dynamic::<usize>::default();

                let _ = actual.reserve_front(256).expect("successful allocation");

                let _ = actual.shrink_back(None).expect("successful deallocation");

                assert_eq!(actual.capacity_front(), 0);
            }

            #[test]
            fn reallocates_memory() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let _ = actual
                    .shrink_back(Some(128))
                    .expect("successful allocation");

                for index in 0..actual.capacity_back() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn does_not_initialize_elements() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let _ = actual
                    .shrink_back(Some(128))
                    .expect("successful reallocation");

                assert_eq!(actual.initialized, 0);
            }

            #[test]
            fn does_not_modify_initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                let _ = actual.shrink_back(None).expect("successful reallocation");

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn zero_capacity_cannot_fail() {
                let mut actual = Dynamic::<usize>::default();

                assert!(actual.shrink_back(None).is_ok());
            }

            #[test]
            fn zero_size_types_cannot_fail() {
                let mut actual = Dynamic::<()>::with_capacity(256).expect("successful allocation");

                assert!(actual.shrink_back(None).is_ok());
            }
        }

        mod shift {
            use super::*;

            #[test]
            fn left_increases_post_capacity_and_decreases_pre_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
                let _ = actual.reserve_front(256).expect("successful allocation");

                for _ in 0..256 {
                    let pre_capacity = actual.pre_capacity;
                    let post_capacity = actual.post_capacity;

                    assert!(actual.shift(-1).is_ok());

                    assert_eq!(actual.pre_capacity, pre_capacity - 1);
                    assert_eq!(actual.post_capacity, post_capacity + 1);
                }
            }

            #[test]
            fn left_does_not_modify_initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected);
                let _ = actual.reserve_front(256).expect("successful allocation");

                for _ in 0..256 {
                    assert!(actual.shift(-1).is_ok());

                    for index in 0..expected.len() {
                        assert_eq!(actual[index], expected[index]);
                    }
                }
            }

            #[test]
            fn right_increases_pre_capacity_and_decreases_post_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
                let _ = actual.reserve_back(256).expect("successful allocation");

                for _ in 0..256 {
                    let pre_capacity = actual.pre_capacity;
                    let post_capacity = actual.post_capacity;

                    assert!(actual.shift(1).is_ok());

                    assert_eq!(actual.pre_capacity, pre_capacity + 1);
                    assert_eq!(actual.post_capacity, post_capacity - 1);
                }
            }

            #[test]
            fn right_does_not_modify_initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected);
                let _ = actual.reserve_back(256).expect("successful allocation");

                for _ in 0..256 {
                    assert!(actual.shift(1).is_ok());

                    for index in 0..expected.len() {
                        assert_eq!(actual[index], expected[index]);
                    }
                }
            }

            #[test]
            fn zero_cannot_fail() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                assert!(actual.shift(0).is_ok())
            }

            #[test]
            fn errors_when_out_of_bounds() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                assert!(actual.shift(-1).is_err());
                assert!(actual.shift(1).is_err());
            }

            #[test]
            fn when_empty() {
                let mut actual = Dynamic::<()>::default();

                assert!(actual.shift(0).is_ok())
            }
        }

        mod drain {
            use super::*;

            #[test]
            fn ok_when_range_is_in_bounds() {
                let actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                for start in 0..actual.len() {
                    for end in (start + 1)..actual.len() {
                        let mut actual = actual.clone();

                        assert!(actual.drain(start..end).is_ok());
                    }
                }
            }

            #[test]
            fn errors_when_start_out_of_bounds() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                assert!(actual.drain(actual.len()..).is_err());
            }

            #[test]
            fn errors_when_end_out_of_bounds() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                assert!(actual.drain(..actual.len() + 1).is_err());
            }

            #[test]
            fn errors_when_empty() {
                let mut actual = Dynamic::<()>::default();

                assert!(actual.drain(..).is_err())
            }

            mod iterator {
                use super::*;

                #[test]
                fn element_count() {
                    let mut expected = vec![0, 1, 2, 3, 4, 5];
                    let mut actual = Dynamic::from_iter(expected.iter().copied());

                    assert_eq!(
                        actual.drain(1..4).expect("valid range").count(),
                        expected.drain(1..4).count()
                    );
                }

                #[test]
                fn in_order() {
                    let mut expected = vec![0, 1, 2, 3, 4, 5];
                    let mut actual = Dynamic::from_iter(expected.iter().copied());

                    assert!(actual
                        .drain(1..4)
                        .expect("valid range")
                        .eq(expected.drain(1..4)));
                }

                mod double_ended {
                    use super::*;

                    #[test]
                    fn element_count() {
                        let mut expected = vec![0, 1, 2, 3, 4, 5];
                        let mut actual = Dynamic::from_iter(expected.iter().copied());

                        assert_eq!(
                            actual.drain(1..4).expect("valid range").rev().count(),
                            expected.drain(1..4).rev().count()
                        );
                    }

                    #[test]
                    fn in_order() {
                        let mut expected = vec![0, 1, 2, 3, 4, 5];
                        let mut actual = Dynamic::from_iter(expected.iter().copied());

                        assert!(actual
                            .drain(1..4)
                            .expect("valid range")
                            .rev()
                            .eq(expected.drain(1..4).rev()));
                    }
                }

                mod exact_size {
                    use super::*;

                    #[test]
                    fn hint() {
                        let mut expected = vec![0, 1, 2, 3, 4, 5];
                        let mut actual = Dynamic::from_iter(expected.iter().copied());

                        let expected = expected.drain(1..4);

                        assert_eq!(
                            actual.drain(1..4).expect("valid range").size_hint(),
                            (expected.len(), Some(expected.len()))
                        );
                    }

                    #[test]
                    fn len() {
                        let mut expected = vec![0, 1, 2, 3, 4, 5];
                        let mut actual = Dynamic::from_iter(expected.iter().copied());

                        assert_eq!(
                            actual.drain(1..4).expect("valid range").len(),
                            expected.drain(1..4).len()
                        );
                    }
                }

                mod fused {
                    use super::*;

                    #[test]
                    fn exhausted() {
                        let mut actual = Dynamic::from_iter([()].iter());
                        let mut actual = actual.drain(0..=0).expect("valid range");

                        // Exhaust the elements.
                        let _ = actual.next().expect("the one element");

                        // Yields `None` at least once.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);

                        // Continues to yield `None`.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }
                }
            }

            mod drop {
                use super::*;

                #[test]
                fn increases_front_capacity_when_front() {
                    let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(..3).expect("valid range"));

                    assert_eq!(actual.capacity_front(), 3);
                }

                #[test]
                fn increases_back_capacity_when_back() {
                    let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(3..).expect("valid range"));

                    assert_eq!(actual.capacity_back(), 3);
                }

                #[test]
                fn increases_capacity_when_middle() {
                    let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(2..=3).expect("valid range"));

                    assert_eq!(actual.capacity(), 2);
                }

                #[test]
                fn removes_yielded_elements() {
                    let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(..).expect("valid range"));

                    assert_eq!(actual.len(), 0);
                    assert_eq!(actual.capacity(), 6);
                }

                #[test]
                fn does_not_modify_leading_elements() {
                    let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(3..).expect("valid range"));

                    assert!(actual.iter().eq([0, 1, 2].iter()));
                }

                #[test]
                fn does_not_modify_trailing_elements() {
                    let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(..3).expect("valid range"));

                    assert!(actual.iter().eq([3, 4, 5].iter()));
                }

                #[test]
                fn shifts_trailing_elements_after_leading_when_mostly_front() {
                    let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(1..=2).expect("valid range"));

                    assert!(actual.iter().eq([0, 3, 4, 5].iter()));
                }

                #[test]
                fn shifts_leading_elements_before_trailing_when_mostly_back() {
                    let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.drain(3..=4).expect("valid range"));

                    assert!(actual.iter().eq([0, 1, 2, 5].iter()));
                }
            }
        }

        mod withdraw {
            use super::*;

            mod iterator {
                use super::*;

                #[test]
                fn element_count() {
                    let mut underlying = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    let actual = underlying.withdraw(|element| element % 2 == 0);

                    assert_eq!(actual.count(), 3);
                }

                #[test]
                fn in_order() {
                    let mut underlying = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    let actual = underlying.withdraw(|element| element % 2 == 0);

                    assert!(actual.eq([0, 2, 4]));
                }

                #[test]
                fn increases_front_capacity_when_withdrawing_first_element() {
                    let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.withdraw(|element| element != &5));

                    assert_eq!(actual.capacity_front(), 5);
                    assert_eq!(actual.capacity_back(), 0);
                }

                #[test]
                fn increases_back_capacity_when_retained_are_combined() {
                    let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.withdraw(|element| element % 2 == 1));

                    assert_eq!(actual.capacity_front(), 0);
                    assert_eq!(actual.capacity_back(), 3);
                }

                #[test]
                fn combines_retained_elements() {
                    let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.withdraw(|element| element == &1));

                    assert!(actual.eq([0, 2, 3, 4, 5]));
                }

                #[test]
                fn first_retained_element_is_not_repositioned() {
                    let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    let first_odd_number = unsafe { actual.as_mut_ptr().add(1) };

                    drop(actual.withdraw(|element| element % 2 == 0));

                    assert_eq!(actual.as_mut_ptr(), first_odd_number);
                }

                #[test]
                fn size_hint() {
                    let mut underlying = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    let actual = underlying.withdraw(|element| element % 2 == 0);

                    assert_eq!(actual.size_hint(), (0, Some(6)));
                }

                mod double_ended {
                    use super::*;

                    #[test]
                    fn element_count() {
                        let mut underlying = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                        let actual = underlying.withdraw(|element| element % 2 == 0).rev();

                        assert_eq!(actual.count(), 3);
                    }

                    #[test]
                    fn in_order() {
                        let mut underlying = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                        let actual = underlying.withdraw(|element| element % 2 == 0).rev();

                        assert!(actual.eq([4, 2, 0]));
                    }

                    #[test]
                    fn increases_back_capacity_when_withdrawing_last_element() {
                        let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                        drop(actual.withdraw(|element| element > &0).rev());

                        assert_eq!(actual.capacity_front(), 0);
                        assert_eq!(actual.capacity_back(), 5);
                    }

                    #[test]
                    fn increases_back_capacity_when_retained_are_combined() {
                        let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                        drop(actual.withdraw(|element| element % 2 == 1).rev());

                        assert_eq!(actual.capacity_front(), 0);
                        assert_eq!(actual.capacity_back(), 3);
                    }

                    #[test]
                    fn combines_retained_elements() {
                        let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                        drop(actual.withdraw(|element| element == &1).rev());

                        assert!(actual.eq([0, 2, 3, 4, 5]));
                    }

                    #[test]
                    fn prevents_elements_from_being_yielded_more_than_once() {
                        let mut underlying = Dynamic::from_iter([0, 1, 2, 0]);

                        let mut actual = underlying.withdraw(|element| element != &0);

                        // make head and tail meet.
                        let _ = actual.next().expect("the element with value '1'");
                        let _ = actual.next_back().expect("the element with value '2'");

                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }
                }

                mod fused {
                    use super::*;

                    #[test]
                    fn empty() {
                        let mut underlying = Dynamic::from_iter([0]);
                        let mut actual = underlying.withdraw(|element| element % 2 == 0);

                        // Exhaust the elements.
                        let _ = actual.next().expect("the one element");

                        // Yields `None` at least once.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);

                        // Continues to yield `None`.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }

                    #[test]
                    fn exhausted() {
                        let mut underlying = Dynamic::<usize>::default();
                        let mut actual = underlying.withdraw(|element| element % 2 == 0);

                        // Yields `None` at least once.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);

                        // Continues to yield `None`.
                        assert_eq!(actual.next(), None);
                        assert_eq!(actual.next_back(), None);
                    }
                }
            }

            mod drop {
                use super::*;

                #[test]
                fn drops_yet_to_be_yielded_elements() {
                    let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                    drop(actual.withdraw(|element| element % 2 == 0));

                    assert!(actual.eq([1, 3, 5]));
                }

                #[test]
                fn combines_trailing_retained_with_beginning_retained() {
                    let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5, 6, 7]);

                    let mut iter = actual.withdraw(|element| element == &3 || element == &4);

                    // Create two regions of retained elements: the first
                    // region contains [0, 1, 2]; the element with value '3'
                    // has been dropped and is not initialized; the second
                    // region contains [5, 6, 7]. Both ends of the iterator
                    // have been exhausted, yet the underlying buffer contains
                    // a gap between two groups of retained elements.
                    let _ = iter.next_back().expect("the element with value '4'");
                    let _ = iter.next().expect("the element with value '3'");

                    // The above means it is now the responsibility of `drop`
                    // to combine these two regions thereby fixing the state of
                    // the underlying buffer for future use.
                    drop(iter);
                }
            }
        }

        mod retain {
            use super::*;

            #[test]
            fn increases_capacity() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                actual.retain(|element| element % 2 == 0);

                assert_eq!(actual.capacity(), 3);
            }

            #[test]
            fn retains_matching_elements_in_order() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                actual.retain(|element| element % 2 == 0);

                assert!(actual.eq([0, 2, 4]));
            }

            #[test]
            fn shifts_trailing_elements_after_first_retained() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                let expected = actual.as_ptr();

                actual.retain(|element| element % 2 == 0);

                assert_eq!(actual.as_ptr(), expected);
            }
        }

        mod resize {
            use super::*;

            #[test]
            fn does_not_initialize_elements() {
                let mut actual = Dynamic::<usize>::default();

                let _ = actual.resize(256).expect("successful allocation");

                assert_eq!(actual.initialized, 0);
            }

            #[test]
            fn increases_post_capacity() {
                let mut actual = Dynamic::<usize>::default();

                let _ = actual.resize(256).expect("successful allocation");

                assert_eq!(actual.post_capacity, 256);
            }

            #[test]
            fn does_not_increase_pre_capacity() {
                let mut actual = Dynamic::<usize>::default();

                let _ = actual.resize(256).expect("successful allocation");

                assert_eq!(actual.pre_capacity, 0);
            }

            #[test]
            fn decreases_post_capacity() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let _ = actual.resize(-128).expect("successful allocation");

                assert_eq!(actual.post_capacity, 128);
            }

            #[test]
            fn does_not_decrease_pre_capacity() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let _ = actual.resize(-128).expect("successful allocation");

                assert_eq!(actual.pre_capacity, 0);
            }

            #[test]
            fn errors_when_input_would_drop_initialized_elements() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                for elements in 1..=actual.initialized {
                    let elements = isize::try_from(elements).unwrap();

                    assert!(actual.resize(-elements).is_err());
                }
            }

            #[test]
            fn allocates_memory() {
                let mut actual = Dynamic::<usize>::default();

                let _ = actual.resize(256).expect("successful allocation");

                for index in 0..actual.capacity_back() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn reallocates_memory() {
                let mut actual =
                    Dynamic::<usize>::with_capacity(256).expect("successful allocation");

                let _ = actual.resize(-128).expect("successful reallocation");

                for index in 0..actual.capacity_back() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn does_not_modify_initialized_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                let _ = actual.resize(128).expect("successful reallocation");

                for index in 0..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn zero_capacity_cannot_fail() {
                let mut actual = Dynamic::<usize>::default();

                assert!(actual.resize(0).is_ok());
            }

            #[test]
            fn zero_size_types_cannot_fail() {
                let mut actual = Dynamic::<()>::with_capacity(256).expect("successful allocation");

                assert!(actual.resize(128).is_ok());
                assert!(actual.resize(-128).is_ok());
            }
        }
    }

    mod drop {
        use super::*;

        #[test]
        fn zero_size_type() {
            drop(Dynamic::<()>::default());
        }

        #[test]
        fn empty() {
            drop(Dynamic::<usize>::default());
        }

        #[test]
        fn all_initialized() {
            let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
            let _ = actual.shrink(None).expect("no capacity");

            drop(actual);
        }

        #[test]
        fn all_front_capacity() {
            let mut actual = Dynamic::<usize>::default();

            let _ = actual.reserve_front(256).expect("successful allocation");

            drop(actual);
        }

        #[test]
        fn all_back_capacity() {
            let mut actual = Dynamic::<usize>::default();

            let _ = actual.reserve_back(256).expect("successful allocation");

            drop(actual);
        }

        #[test]
        fn front_capacity_and_initialized_elements_and_back_capacity() {
            let mut actual = Dynamic::<usize>::from_iter([0, 1, 2, 3, 4, 5]);

            let _ = actual.reserve_front(256).expect("successful allocation");
            let _ = actual.reserve_back(256).expect("successful allocation");

            drop(actual);
        }
    }

    mod try_from {
        use super::*;

        #[test]
        fn does_not_allocate_front_capacity() {
            let expected = [0, 1, 2, 3, 4, 5];
            let actual = Dynamic::try_from(expected.as_slice()).expect("successful allocation");

            assert_eq!(actual.pre_capacity, 0);
        }

        #[test]
        fn does_not_allocate_back_capacity() {
            let expected = [0, 1, 2, 3, 4, 5];
            let actual = Dynamic::try_from(expected.as_slice()).expect("successful allocation");

            assert_eq!(actual.post_capacity, 0);
        }

        #[test]
        fn allocates_memory() {
            let expected = [0, 1, 2, 3, 4, 5];
            let actual = Dynamic::try_from(expected.as_slice()).expect("successful allocation");

            for index in 0..expected.len() {
                unsafe {
                    let ptr = actual.buffer.as_ptr().add(index);

                    // Ideally, this will seg-fault if unowned memory.
                    let _ = (*ptr).write(index);
                }
            }
        }

        #[test]
        fn has_elements() {
            let expected = [0, 1, 2, 3, 4, 5];
            let actual = Dynamic::try_from(expected.as_slice()).expect("successful allocation");

            assert_eq!(actual.initialized, expected.len());
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

            let _ = instance.index(0);
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

            let _ = instance.index_mut(0);
        }
    }

    mod iterator {
        use super::*;

        struct FaultySizeHintIter<I> {
            data: std::iter::Copied<I>,
        }

        impl<'a, T: 'a + Copy, I> Iterator for FaultySizeHintIter<I>
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
                    let _ = actual.next().expect("the one element");

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
            fn does_not_allocate_front_capacity() {
                let actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                assert_eq!(actual.pre_capacity, 0);
            }

            #[test]
            fn does_not_allocate_back_capacity() {
                let actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                assert_eq!(actual.post_capacity, 0);
            }

            #[test]
            fn allocates_memory() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Dynamic::from_iter(expected.iter().copied());

                for index in 0..expected.len() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn has_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Dynamic::from_iter(expected.iter().copied());

                assert_eq!(actual.initialized, expected.len());
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

            #[test]
            fn does_not_trust_size_hint() {
                let expected = [0, 1, 2, 3, 4, 5];

                // Ideally, this will panic if it uses the invalid size.
                let _actual = Dynamic::from_iter(FaultySizeHintIter {
                    data: expected.iter().copied(),
                });
            }
        }

        mod extend {
            use super::*;

            #[test]
            fn does_not_allocate_front_capacity() {
                let mut actual = Dynamic::<usize>::default();

                let expected = [0, 1, 2, 3, 4, 5];
                actual.extend(expected);

                assert_eq!(actual.pre_capacity, 0);
            }

            #[test]
            fn does_not_allocate_back_capacity() {
                let mut actual = Dynamic::<usize>::default();

                let expected = [0, 1, 2, 3, 4, 5];
                actual.extend(expected);

                assert_eq!(actual.post_capacity, 0);
            }

            #[test]
            fn consumes_front_capacity() {
                let mut actual = Dynamic::<usize>::default();

                let expected = [0, 1, 2, 3, 4, 5];

                let _ = actual
                    .reserve_front(expected.len())
                    .expect("successful allocation");

                actual.extend(expected);

                assert_eq!(actual.capacity_front(), 0);
            }

            #[test]
            fn consumes_back_capacity() {
                let mut actual = Dynamic::<usize>::default();

                let expected = [0, 1, 2, 3, 4, 5];

                let _ = actual
                    .reserve_back(expected.len())
                    .expect("successful allocation");

                actual.extend(expected);

                assert_eq!(actual.capacity_back(), 0);
            }

            #[test]
            fn allocates_memory_when_empty() {
                let mut actual = Dynamic::<usize>::default();

                let expected = [0, 1, 2, 3, 4, 5];
                actual.extend(expected);

                for index in 0..expected.len() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn reallocates_memory_when_not_enough_capacity() {
                let mut actual = Dynamic::<usize>::with_capacity(1).expect("successful allocation");

                let expected = [0, 1, 2, 3, 4, 5];
                actual.extend(expected);

                for index in 0..expected.len() {
                    unsafe {
                        let ptr = actual.buffer.as_ptr().add(index);

                        // Ideally, this will seg-fault if unowned memory.
                        let _ = (*ptr).write(index);
                    }
                }
            }

            #[test]
            fn has_elements() {
                let mut actual = Dynamic::default();

                let expected = [0, 1, 2, 3, 4, 5];
                actual.extend(expected);

                assert_eq!(actual.initialized, expected.len());
            }

            #[test]
            fn initializes_elements() {
                let mut actual = Dynamic::default();

                let expected = [0, 1, 2, 3, 4, 5];
                actual.extend(expected);

                for index in 0..expected.len() {
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
            fn appends_after_initialized_elements() {
                let initialized = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(initialized.iter().copied());

                let expected = [6, 7, 8, 9, 10];
                actual.extend(expected.iter().copied());

                for index in initialized.len()..expected.len() {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn empty() {
                let mut actual = Dynamic::<()>::default();

                actual.extend(std::iter::empty());

                assert_eq!(actual.pre_capacity, 0);
                assert_eq!(actual.initialized, 0);
                assert_eq!(actual.post_capacity, 0);
            }

            #[test]
            fn does_not_trust_size_hint() {
                let mut actual = Dynamic::<usize>::default();

                let expected = [0, 1, 2, 3, 4, 5];

                // Ideally, this will panic if it uses the invalid size.
                actual.extend(FaultySizeHintIter {
                    data: expected.iter().copied(),
                });
            }
        }
    }

    mod default {
        use super::*;

        #[test]
        fn does_not_allocate_front_capacity() {
            let actual = Dynamic::<usize>::default();

            assert_eq!(actual.pre_capacity, 0);
        }

        #[test]
        fn does_not_allocate_back_capacity() {
            let actual = Dynamic::<usize>::default();

            assert_eq!(actual.post_capacity, 0);
        }

        #[test]
        fn does_not_initialize_elements() {
            let actual = Dynamic::<()>::default();

            assert_eq!(actual.initialized, 0);
        }
    }

    mod clone {
        use super::*;

        #[test]
        fn does_not_allocate_front_capacity() {
            let actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]).clone().clone();

            assert_eq!(actual.pre_capacity, 0);
        }

        #[test]
        fn does_not_allocate_back_capacity() {
            let actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]).clone().clone();

            assert_eq!(actual.post_capacity, 0);
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
        fn ignores_different_front_capacity() {
            let expected = [0, 1, 2, 3, 4, 5];

            let mut first = Dynamic::from_iter(expected.iter().copied());
            let mut second = Dynamic::from_iter(expected.iter().copied());

            let _ = first.reserve_front(128).expect("successful allocation");
            let _ = second.reserve_front(256).expect("successful allocation");

            assert_eq!(first, second);
        }

        #[test]
        fn ignores_different_back_capacity() {
            let expected = [0, 1, 2, 3, 4, 5];

            let mut first = Dynamic::from_iter(expected.iter().copied());
            let mut second = Dynamic::from_iter(expected.iter().copied());

            let _ = first.reserve_back(128).expect("successful allocation");
            let _ = second.reserve_back(256).expect("successful allocation");

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

    mod fmt {
        use super::*;

        mod debug {
            use super::*;

            #[test]
            fn is_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let actual = Dynamic::from_iter(expected.iter().cloned());

                assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
            }
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
            fn ignores_front_capacity() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual = Dynamic::from_iter(expected.iter().copied());

                let _ = actual.reserve_front(256).expect("successful allocation");

                assert_eq!(actual.count(), expected.len());
            }

            #[test]
            fn ignores_back_capacity() {
                let expected = [0, 1, 2, 3, 4, 5];

                let mut actual = Dynamic::from_iter(expected.iter().copied());

                let _ = actual.reserve_back(256).expect("successful allocation");

                assert_eq!(actual.count(), expected.len());
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
                    let _ = actual.next().expect("the one element");

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
                    let _ = actual.next().expect("the one element");

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
            fn address_of_underlying_buffer() {
                let actual = Dynamic::<i32>::from_iter([0, 1, 2, 3, 4, 5]);

                assert_eq!(
                    actual.as_ptr(),
                    actual.buffer.as_ptr().cast::<i32>().cast_const()
                );
            }

            #[test]
            fn skips_front_capacity() {
                let mut actual = Dynamic::<i32>::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_front(256).expect("successful allocation");

                assert_eq!(actual.as_ptr(), unsafe {
                    actual.buffer.as_ptr().cast::<i32>().cast_const().add(256)
                });
            }

            #[test]
            #[should_panic]
            fn panics_if_no_allocation() {
                let actual = Dynamic::<()>::default();

                let _ = actual.as_ptr();
            }
        }

        mod as_mut_ptr {
            use super::*;

            #[test]
            fn address_of_underlying_buffer() {
                let mut actual = Dynamic::<i32>::from_iter([0, 1, 2, 3, 4, 5]);

                assert_eq!(actual.as_mut_ptr(), actual.buffer.as_ptr().cast::<i32>());
            }

            #[test]
            fn skips_front_capacity() {
                let mut actual = Dynamic::<i32>::from_iter([0, 1, 2, 3, 4, 5]);

                let _ = actual.reserve_front(256).expect("successful allocation");

                assert_eq!(actual.as_mut_ptr(), unsafe {
                    actual.buffer.as_ptr().cast::<i32>().add(256)
                });
            }

            #[test]
            #[should_panic]
            fn panics_if_no_allocation() {
                let mut actual = Dynamic::<()>::default();

                let _ = actual.as_mut_ptr();
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

                let _ = actual.insert(2, 12345).expect("successful allocation");

                assert_eq!(actual.initialized, expected.len() + 1);
            }

            #[test]
            fn initializes_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                let _ = actual.insert(2, 12345).expect("successful allocation");

                assert_eq!(actual[2], 12345);
            }

            #[test]
            fn yields_inserted_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                let actual = actual.insert(2, 12345).expect("successful allocation");

                assert_eq!(actual, &mut 12345);
            }

            #[test]
            fn will_allocate_when_empty() {
                let mut actual = Dynamic::<usize>::default();

                assert!(actual.insert(0, 12345).is_ok());
            }

            #[test]
            fn will_reallocate_when_no_capacity() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());
                let _ = actual.shrink(None).expect("no capacity");

                assert!(actual.insert(2, 12345).is_ok());
            }

            #[test]
            fn does_not_modify_leading_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                const INDEX: usize = 2;
                let _ = actual.insert(INDEX, 12345).expect("successful allocation");

                for index in 0..INDEX {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn does_not_modify_trailing_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                const INDEX: usize = 2;
                let _ = actual.insert(INDEX, 12345).expect("successful allocation");

                for index in INDEX..expected.len() {
                    assert_eq!(actual[index + 1], expected[index]);
                }
            }

            #[test]
            fn can_prepend() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                assert!(actual.insert(0, 12345).is_ok());
            }

            #[test]
            fn prepending_consumes_front_capacity_when_not_empty() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
                let _ = actual.reserve_front(1).expect("successful allocation");

                let _ = actual.insert(0, 12345).expect("uses front capacity");

                assert_eq!(actual.capacity_front(), 0);
            }

            #[test]
            fn prepending_consumes_back_capacity_when_empty() {
                let mut actual = Dynamic::<usize>::default();
                let _ = actual.reserve_back(1).expect("successful allocation");

                let _ = actual.insert(0, 12345).expect("uses back capacity");

                assert_eq!(actual.capacity_back(), 0);
            }

            #[test]
            fn can_append() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                assert!(actual.insert(6, 12345).is_ok());
            }

            #[test]
            fn appending_consumes_back_capacity_when_not_empty() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);
                let _ = actual.reserve_back(1).expect("successful allocation");

                let _ = actual.insert(6, 12345).expect("uses back capacity");

                assert_eq!(actual.capacity_back(), 0);
            }

            #[test]
            fn appending_consumes_front_capacity_when_empty() {
                let mut actual = Dynamic::<usize>::default();
                let _ = actual.reserve_front(1).expect("successful allocation");

                let _ = actual.insert(0, 12345).expect("uses front capacity");

                assert_eq!(actual.capacity_front(), 0);
            }
        }

        mod remove {
            use super::*;

            #[test]
            fn subtracts_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                let _ = actual.remove(0);

                assert_eq!(actual.initialized, expected.len() - 1);
            }

            #[test]
            fn yields_element() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                for index in 0..expected.len() {
                    assert_eq!(actual.remove(0).expect("front element"), expected[index]);
                }
            }

            #[test]
            fn does_not_modify_leading_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                const INDEX: usize = 2;
                let _ = actual.remove(INDEX);

                for index in 0..INDEX {
                    assert_eq!(actual[index], expected[index]);
                }
            }

            #[test]
            fn does_not_modify_trailing_elements() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected.iter().copied());

                const INDEX: usize = 2;
                let _ = actual.remove(INDEX);

                for index in INDEX..expected.len() - 1 {
                    assert_eq!(actual[index], expected[index + 1]);
                }
            }

            #[test]
            fn none_when_index_out_of_bounds() {
                let mut actual = Dynamic::<()>::default();

                assert!(actual.remove(0).is_none());
            }

            #[test]
            fn increases_front_capacity_if_first_element() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                for index in 0..actual.len() {
                    let _ = actual.remove(0).expect("element to remove");

                    assert_eq!(actual.capacity_front(), index + 1);
                }
            }
        }

        mod clear {
            use super::*;

            #[test]
            fn drop_all_elements() {
                let mut actual = Dynamic::from_iter([0, 1, 2, 3, 4, 5]);

                actual.clear();

                assert_eq!(actual.initialized, 0);
            }

            #[test]
            fn keeps_allocation() {
                let expected = [0, 1, 2, 3, 4, 5];
                let mut actual = Dynamic::from_iter(expected);

                actual.clear();

                assert_eq!(actual.capacity(), expected.len());
            }

            #[test]
            fn when_already_empty() {
                let mut actual = Dynamic::<usize>::default();

                // Ideally this will panic or something in case of logic error.
                actual.clear();
            }
        }
    }
}
