//! Implementation of [`Dynamic`].

use super::Array;
use super::Collection;
use super::Linear;
use super::LinearMut;

/// Error type for when allocation fails.
#[derive(Debug)]
pub struct AllocationError;

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
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory for the result.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let instance = Dynamic::<()>::new();
    ///
    /// assert_eq!(instance.len(), 0);
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
    /// This may allocate more capacity than requested.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(N) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let instance = Dynamic::<()>::with_capacity(4).unwrap();
    ///
    /// assert_eq!(instance.len(), 0);
    /// assert!(instance.capacity() >= 4);
    /// ```
    pub fn with_capacity(count: usize) -> Result<Self, ()> {
        let mut instance = Self::new();
        if instance.reserve(count) {
            Ok(instance)
        } else {
            Err(())
        }
    }

    /// Query how many elements could be inserted without allocation.
    ///
    /// # Performance
    /// This methods takes O(1) time and consumes O(1) memory.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::<i32>::with_capacity(2).unwrap();
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
    /// This may allocate more capacity than requested, in which case the
    /// result yields the actual capacity reserved.
    ///
    /// # Panics
    /// Rust runtime might panic if allocation fails.
    ///
    /// # Performance
    /// This methods takes O(N) time and consumes O(N) memory.
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
    pub fn reserve(&mut self, capacity: usize) -> Result<usize, AllocationError> {
        if std::mem::size_of::<T>() == 0 {
            self.allocated = usize::MAX;
            return true;
        }

        if self.allocated > capacity || capacity == 0 {
            return Ok(self.allocated);
        }

        // growth factor of two (2) so capacity is doubled each reallocation.
        let size = match self
            .initialized
            .checked_add(capacity)
            .and_then(|size: usize| size.checked_next_power_of_two())
        {
            Some(size) => size,
            None => return false,
        }
        .next_power_of_two();

        let layout = match std::alloc::Layout::array::<T>(size) {
            Ok(layout) => layout,
            Err(_) => return Err(AllocationError),
        };

        let old_size = self.initialized + self.allocated;

        let ptr = if old_size == 0 {
            // SAFETY: non-zero-size type => `layout` has non-zero size.
            unsafe { std::alloc::alloc(layout) }
        } else {
            let new_size = layout.size();
            let layout = match std::alloc::Layout::array::<T>(old_size) {
                Ok(layout) => layout,
                Err(_) => return Err(AllocationError),
            };

            // SAFETY: non-zero-size type => `layout` has non-zero size.
            unsafe { std::alloc::realloc(self.data.cast::<u8>().as_ptr(), layout, new_size) }
        };

        // SAFETY: [`MaybeUninit<T>`] has the same layout at `T`.
        let ptr = ptr.cast::<std::mem::MaybeUninit<T>>();

        self.data = match std::ptr::NonNull::new(ptr) {
            Some(ptr) => ptr,
            None => return Err(AllocationError),
        };

        self.allocated = size - self.initialized;

        Ok(self.allocated)
    }

    /// Attempt to shrink the capacity to exactly `capacity`, or none/zero.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    ///
    /// let mut instance = Dynamic::<()>::with_capacity(16).unwrap();
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
        let new_size = match std::alloc::Layout::array::<T>(size) {
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

        self.allocated = capacity;

        true
    }

    /// Drop all elements.
    ///
    /// # Examples
    /// ```
    /// use rust::structure::collection::linear::array::Dynamic;
    /// use rust::structure::collection::Collection;
    ///
    /// let mut instance = Dynamic::try_from([0, 1, 2, 3].as_slice());
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

impl<T> std::ops::Drop for Dynamic<T> {
    /// Drops the elements that are initialized and deallocate memory.
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
    pub fn append(&mut self, element: T) -> Result<&mut T, AllocationError> {
        if self.allocated == 0 && !self.reserve(1) {
            return Err(AllocationError);
        }

        unsafe {
            // SAFETY: the buffer has been allocated.
            let ptr = self.data.as_ptr();

            // SAFETY: this points to the first uninitialized element.
            let ptr = ptr.add(self.initialized);

            self.initialized += 1;
            self.allocated -= 1;

            // SAFETY:
            // * `ptr` is non-null.
            // * `ptr` is aligned.
            // * the [`MaybeUninit<T>`] is initialized even if the `T` isn't.
            Ok((*ptr).write(element))
        }
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

impl<'a, T: 'a + Clone> std::convert::TryFrom<&'a [T]> for Dynamic<T> {
    type Error = AllocationError;

    fn try_from(value: &'a [T]) -> Result<Self, Self::Error> {
        let mut instance = match Self::with_capacity(value.len()) {
            Ok(allocation) => allocation,
            Err(_) => return Err(AllocationError),
        };

        for element in value {
            instance
                .append(element.clone())
                .expect("preallocated space");
        }

        Ok(instance)
    }
}

impl<'a, T: 'a> super::Collection<'a> for Dynamic<T> {
    type Element = T;

    fn count(&self) -> usize {
        self.initialized
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

impl<'a, T: 'a> Linear<'a> for Dynamic<T> {
    fn iter(&self) -> impl std::iter::Iterator<Item = &'a Self::Element> {
        unsafe {
            // SAFETY: `MaybeUninit<T>` has the same memory layout as `T`.
            let ptr = self.data.cast::<T>();

            // SAFETY: `ptr` is dangling if and only if no elements have been
            // initialized, in which case the pointer will not be read.
            super::Iter::new(ptr, self.initialized)
        }
    }

    fn iter_mut(&mut self) -> impl std::iter::Iterator<Item = &'a mut Self::Element> {
        unsafe {
            // SAFETY: `MaybeUninit<T>` has the same memory layout as `T`.
            let ptr = self.data.cast::<T>();

            // SAFETY: `ptr` is dangling if and only if no elements have been
            // initialized, in which case the pointer will not be read.
            super::IterMut::new(ptr, self.initialized)
        }
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
        if std::mem::size_of::<T>() == 0 {
            return;
        }

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
            let element = unsafe {
                // SAFETY: `T` has same layout as [`MaybeUninit<T>`].
                let ptr = self.data.as_ptr().cast::<T>();

                // SAFETY: stays aligned within the allocated object.
                let ptr = ptr.add(self.next.start);

                // SAFETY: the element is initialized.
                ptr.read()
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
        // SAFETY: double free if `self` attempts to drop `data`.
        let input = std::mem::ManuallyDrop::new(self);

        IntoIter {
            data: input.data,
            layout: std::alloc::Layout::array::<T>(input.initialized + input.allocated).unwrap(),
            next: 0..input.initialized,
        }
    }
}

impl<'a, T: 'a> LinearMut<'a> for Dynamic<T> {
    fn insert(&mut self, index: usize, element: Self::Element) -> Result<&mut T, Self::Element> {
        if index >= self.initialized {
            return Err(element);
        }

        if self.allocated == 0 && !self.reserve(1) {
            return Err(element);
        }

        // shift initialized elements `[index..]` one position to the right.
        if std::mem::size_of::<T>() != 0 {
            unsafe {
                // SAFETY: aligned within the allocated object.
                let from = self.data.as_ptr().add(index);

                // SAFETY: capacity was confirmed so this is also within the object.
                let to = from.add(1);

                // SAFETY: owned memory and no aliasing despite overlapping.
                std::ptr::copy(from, to, self.initialized - index);
            }
        }

        // SAFETY: update internal state to reflect shift.
        self.initialized += 1;
        self.allocated -= 1;

        unsafe {
            // SAFETY: aligned within the allocated object.
            let ptr = self.data.as_ptr().add(index);

            // SAFETY:
            // * `ptr` points to the uninitialized element created by shifting.
            // * `ptr` is mutably owned.
            Ok((*ptr).write(element))
        }
    }

    fn remove(&mut self, index: usize) -> Option<Self::Element> {
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

impl<'a, T: 'a> Array<'a> for Dynamic<T> {
    unsafe fn as_ptr(&self) -> *const Self::Element {
        if self.initialized + self.allocated == 0 {
            std::ptr::null()
        } else {
            // SAFETY: `MaybeUninit<T>` has same memory layout as `T`.
            self.data.cast::<T>().as_ptr().cast_const()
        }
    }

    unsafe fn as_mut_ptr(&mut self) -> *mut Self::Element {
        if self.initialized + self.allocated == 0 {
            std::ptr::null_mut()
        } else {
            // SAFETY: `MaybeUninit<T>` has same memory layout as `T`.
            self.data.cast::<T>().as_ptr()
        }
    }
}

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
        let mut clone = match Self::with_capacity(self.count()) {
            Ok(allocation) => allocation,
            Err(_) => panic!("allocation failed"),
        };

        for element in self.iter() {
            clone.append(element.clone()).expect("preallocated space");
        }

        clone
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new_does_not_allocate() {
        let instance = Dynamic::<()>::new();

        assert_eq!(instance.initialized, 0);
        assert_eq!(instance.allocated, 0);
    }

    #[test]
    fn from_slice_makes_separate_allocation_for_normal_types() {
        let original = [0, 1, 2, 3, 4, 5];
        let instance = Dynamic::try_from(original.as_slice()).unwrap();

        assert_ne!(instance.data.as_ptr().cast(), original.as_ptr().cast_mut());
    }

    #[test]
    fn from_slice_initializes_member_variables() {
        let original = [(), (), (), (), (), ()];
        let instance = Dynamic::try_from(original.as_slice()).unwrap();

        assert_eq!(instance.initialized, original.len());
        assert!(instance.allocated >= original.len());
    }

    #[test]
    fn from_slice_initializes_elements() {
        let original = [0, 1, 2, 3, 4, 5];
        let instance = Dynamic::try_from(original.as_slice()).unwrap();

        assert!(instance.iter().eq(original.iter()));
    }

    #[test]
    fn with_capacity_increases_capacity() {
        const COUNT: usize = 256;

        let instance = Dynamic::<()>::with_capacity(COUNT).unwrap();

        assert!(instance.capacity() >= COUNT);
    }

    #[test]
    fn with_capacity_does_not_initialize_elements() {
        let instance = Dynamic::<()>::with_capacity(256).unwrap();

        assert_eq!(instance.initialized, 0);
    }

    #[test]
    fn with_capacity_preallocates() {
        const COUNT: usize = 256;

        let mut instance = Dynamic::<usize>::with_capacity(COUNT).unwrap();
        let preallocated = instance.allocated;

        for element in 0..COUNT {
            instance.append(element).expect("preallocated");
        }

        assert_eq!(instance.allocated, preallocated - COUNT);
    }

    #[test]
    fn count_ignores_preallocation() {
        let mut instance = Dynamic::<()>::with_capacity(256).unwrap();
        instance.reserve(1024);

        assert_ne!(instance.count(), instance.allocated)
    }

    #[test]
    fn count_is_element_count() {
        let original = [0, 1, 2, 3, 4, 5];
        let instance = Dynamic::try_from(original.as_slice()).unwrap();

        assert_eq!(instance.count(), original.len());
    }

    #[test]
    fn capacity_increases_with_reservation() {
        let mut instance = Dynamic::<()>::with_capacity(256).unwrap();

        assert!(instance.capacity() >= 256);

        instance.reserve(1024);

        assert!(instance.capacity() >= 1024);
    }

    #[test]
    fn reserve_increases_capacity() {
        const COUNT: usize = 256;

        let mut instance = Dynamic::<()>::new();
        instance.reserve(COUNT);

        assert!(instance.allocated >= COUNT);
    }

    #[test]
    fn reserve_does_not_remove_initialized_elements() {
        let original = [0, 1, 2, 3, 4, 5];
        let mut instance = Dynamic::try_from(original.as_slice()).unwrap();

        instance.reserve(2048);

        assert!(instance.iter().eq(original.as_slice()));
    }

    #[test]
    fn reserve_preallocates() {
        const COUNT: usize = 256;

        let mut instance = Dynamic::<usize>::new();
        instance.reserve(COUNT);

        let preallocated = instance.allocated;

        for element in 0..COUNT {
            instance.append(element).expect("preallocated");
        }

        assert_eq!(instance.allocated, preallocated - COUNT);
    }

    #[test]
    fn reserve_does_not_shrink() {
        const COUNT: usize = 256;

        let mut instance = Dynamic::<()>::with_capacity(COUNT).unwrap();

        instance.reserve(0);

        assert!(instance.allocated >= COUNT);
    }

    #[test]
    fn shrink_to_exact_capacity() {
        let mut instance = Dynamic::<()>::with_capacity(256).unwrap();

        instance.shrink(Some(8));

        assert_eq!(instance.allocated, 8);
    }

    #[test]
    fn shrink_to_no_capacity() {
        let mut instance = Dynamic::<()>::with_capacity(256).unwrap();

        instance.shrink(None);

        assert_eq!(instance.allocated, 0);
    }

    #[test]
    fn shrink_does_not_remove_initialized_elements() {
        let original = [0, 1, 2, 3, 4, 5];
        let mut instance = Dynamic::try_from(original.as_slice()).unwrap();

        instance.shrink(None);

        assert!(instance.iter().eq(original.as_slice()));
    }

    #[test]
    fn append_initializes_an_element() {
        let mut instance = Dynamic::<()>::with_capacity(1).unwrap();

        instance.append(()).expect("appended");

        assert_eq!(instance.initialized, 1);
    }

    #[test]
    fn append_returns_element() {
        let mut instance = Dynamic::<usize>::new();

        let result = *instance.append(0).unwrap();

        assert_eq!(result, *instance.first().unwrap());
    }

    #[test]
    fn append_will_reallocate() {
        let mut instance = Dynamic::<usize>::new();

        instance.append(0).expect("appended");

        assert_eq!(instance.initialized, 1);
    }

    #[test]
    fn append_inserts_at_correct_position() {
        let mut instance = Dynamic::try_from([0, 1, 2, 3, 4, 5].as_slice()).unwrap();

        instance.append(6).expect("appended");

        assert_eq!(*instance.last().unwrap(), 6);
    }

    #[test]
    fn append_preserves_elements_order() {
        let original = [0, 1, 2, 3, 4, 5];
        let mut instance = Dynamic::try_from(original.as_slice()).unwrap();

        instance.append(6).expect("appended");

        assert_eq!(instance.as_slice()[..original.len()], original);
    }

    #[test]
    fn insert_initialized_a_new_element() {
        let mut instance = Dynamic::try_from([()].as_slice()).unwrap();

        instance.insert(0, ()).expect("inserted");

        assert_eq!(instance.initialized, 2);
    }

    #[test]
    fn insert_modifies_element_value() {
        let mut instance = Dynamic::try_from([0].as_slice()).unwrap();

        instance.insert(0, 1).expect("inserted");

        assert_eq!(*instance.first().unwrap(), 1);
    }

    #[test]
    fn insert_returns_element() {
        let mut instance = Dynamic::try_from([256].as_slice()).unwrap();

        let result = *instance.insert(1, 0).unwrap();

        assert_eq!(result, *instance.first().unwrap());
    }

    #[test]
    fn insert_only_modifies_specific_index() {
        let original = [0, 1, 2, 3, 4, 5];
        let instance = Dynamic::try_from(original.as_slice()).unwrap();

        for index in 0..instance.count() {
            let mut instance = instance.clone();
            instance.insert(256, index).expect("inserted");

            assert!(instance.as_slice()[..index]
                .iter()
                .eq(&original.as_slice()[..index]));

            assert!(instance.as_slice()[index + 2..]
                .iter()
                .eq(&original.as_slice()[index + 1..]));
        }
    }

    #[test]
    fn insert_will_reallocate() {
        let mut instance = Dynamic::try_from([0].as_slice()).unwrap();
        instance.shrink(None);

        instance.append(0).expect("inserted");

        assert_eq!(instance.initialized, 2);
    }

    #[test]
    #[should_panic]
    fn insert_panics_when_out_of_bounds() {
        let mut instance = Dynamic::<()>::new();

        instance.insert(0, ()).expect("inserted");
    }

    #[test]
    fn remove_drops_an_element() {
        let mut instance = Dynamic::try_from([0].as_slice()).unwrap();

        instance.remove(0);

        assert_eq!(instance.initialized, 0);
    }

    #[test]
    fn remove_increases_capacity() {
        let mut instance = Dynamic::try_from([0].as_slice()).unwrap();
        let preallocated = instance.allocated;

        instance.remove(0);

        assert_eq!(instance.allocated, preallocated + 1);
    }

    #[test]
    fn remove_returns_element_value() {
        let mut instance = Dynamic::try_from([256].as_slice()).unwrap();

        let result = instance.remove(0);

        assert_eq!(result.unwrap(), 256);
    }

    #[test]
    fn remove_keeps_other_elements() {
        let original = vec![0, 1, 2, 3, 4, 5];

        for index in 0..original.len() {
            let mut original = original.clone();
            let mut instance = Dynamic::try_from(original.as_slice()).unwrap();
            original.remove(index);

            instance.remove(index);

            assert!(instance.into_iter().eq(original));
        }
    }

    #[test]
    fn remove_none_when_out_of_bounds() {
        let mut instance = Dynamic::<()>::new();

        assert_eq!(instance.remove(0), None);
    }

    #[test]
    fn clear_drops_elements() {
        let mut instance = Dynamic::try_from([0, 1, 2, 3, 4].as_slice()).unwrap();

        instance.clear();

        assert_eq!(instance.initialized, 0);
    }

    #[test]
    fn clear_increases_capacity() {
        let mut instance = Dynamic::try_from([(), (), (), (), (), ()].as_slice()).unwrap();
        let elements = instance.initialized;
        let preallocated = instance.allocated;

        instance.clear();

        assert_eq!(instance.allocated, preallocated + elements);
    }

    #[test]
    fn into_iter_yields_element_count() {
        let original = [0, 1, 2, 3, 4, 5];
        let instance = Dynamic::try_from(original.as_slice()).unwrap();

        assert_eq!(instance.into_iter().count(), original.into_iter().count());
    }

    #[test]
    fn into_iter_yields_elements() {
        let original = [0, 1, 2, 3, 4, 5];
        let instance = Dynamic::try_from(original.as_slice()).unwrap();

        assert!(instance.into_iter().eq(original.into_iter()));
    }

    #[test]
    fn iter_yields_element_count() {
        let original = [0, 1, 2, 3, 4, 5];
        let instance = Dynamic::try_from(original.as_slice()).unwrap();

        assert_eq!(instance.iter().count(), original.iter().count());
    }

    #[test]
    fn iter_yields_elements() {
        let original = [0, 1, 2, 3, 4, 5];
        let instance = Dynamic::try_from(original.as_slice()).unwrap();

        assert!(instance.iter().eq(original.iter()));
    }

    #[test]
    fn iter_mut_yields_element_count() {
        let mut original = [0, 1, 2, 3, 4, 5];
        let mut instance = Dynamic::try_from(original.as_slice()).unwrap();

        assert_eq!(instance.iter_mut().count(), original.iter_mut().count());
    }

    #[test]
    fn iter_mut_yields_elements() {
        let mut original = [0, 1, 2, 3, 4, 5];
        let mut instance = Dynamic::try_from(original.as_slice()).unwrap();

        assert!(instance.iter_mut().eq(original.iter_mut()));
    }

    #[test]
    fn index_yields_correct_element() {
        let original = [0, 1, 2, 3, 4, 5];
        let instance = Dynamic::try_from(original.as_slice()).unwrap();

        for (index, value) in original.iter().enumerate() {
            use std::ops::Index;
            assert_eq!(instance.index(index), value);
        }
    }

    #[test]
    #[should_panic]
    fn index_panics_when_out_of_bounds() {
        let instance = Dynamic::<()>::new();

        use std::ops::Index;
        instance.index(0);
    }

    #[test]
    fn index_mut_yields_correct_element() {
        let original = [0, 1, 2, 3, 4, 5];
        let mut instance = Dynamic::try_from(original.as_slice()).unwrap();

        for (index, value) in original.iter().enumerate() {
            use std::ops::IndexMut;
            assert_eq!(instance.index_mut(index), value);
        }
    }

    #[test]
    #[should_panic]
    fn index_mut_panics_when_out_of_bounds() {
        let mut instance = Dynamic::<()>::new();

        use std::ops::IndexMut;
        instance.index_mut(0);
    }

    #[test]
    fn eq_for_same_elements() {
        let original = [0, 1, 2, 3, 4, 5];

        let instance = Dynamic::try_from(original.as_slice()).unwrap();
        let other = Dynamic::try_from(original.as_slice()).unwrap();

        assert_eq!(instance, other);
    }

    #[test]
    fn ne_for_different_elements() {
        let instance = Dynamic::try_from([0].as_slice()).unwrap();
        let other = Dynamic::try_from([1].as_slice()).unwrap();

        assert_ne!(instance, other);
    }

    #[test]
    fn default_does_not_allocate() {
        let instance: Dynamic<()> = Default::default();

        assert_eq!(instance.initialized, 0);
        assert_eq!(instance.allocated, 0);
    }

    #[test]
    fn clone_is_eq() {
        let original = Dynamic::try_from([0, 1, 2, 3, 4, 5].as_slice()).unwrap();

        let clone = original.clone();

        assert_eq!(clone, original);
    }
}
