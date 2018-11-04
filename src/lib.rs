use std::collections::{HashMap, hash_map::{Entry, Iter as HashMapIter, Drain as HashMapDrain, RandomState}};
use std::hash::{Hash, BuildHasher};
use std::iter::{FromIterator, FusedIterator};
use std::borrow::Borrow;
use std::cmp::{max, min};
use std::ops::{Add, Sub};
use std::marker::PhantomData;


/// A multiset built on top of `std::collections::HashMap`. Tries to maintain
/// compatibility with `std::collections::HashSet` where it makes sense.
///
/// All the requirements on `std::collections::HashMap` apply. To summarize,
/// elements must implement [`Eq`] and [`Hash`]. It is also logic error for an
/// item to be modified in such a way that the its hash, as determined by the
/// `std::hash::Hash` trait, or its equality, as determined by the
/// `std::cmp::Eq` trait, changes while it is in the set.
///
/// The data structure strives to keep compatibility with
/// `std::collections::HashSet`, however this is not always possible or logical.
/// Below is a list of all the differences between `std::collections::HashSet`
/// and [`MultiHashSet`]:
/// # Examples
/// ```rust
/// # extern crate multi_collections;
/// # use multi_collections::MultiHashSet;
/// fn main() {
///     let names: MultiHashSet<&'static str> =
///         ["Tom", "Tom", "Dick"].iter().cloned().collect();
///     assert_eq!(names.get_count("Tom"), 2);
///     assert_eq!(names.get_count("Dick"), 1);
///     assert_eq!(names.get_count("Larry"), 0);
///     assert_eq!(names.len(), 2);
///     assert_eq!(names.size(), 3);
/// }
/// ```
#[derive(Clone, Debug)]
pub struct MultiHashSet<T: Eq + Hash, S : BuildHasher = RandomState> {
    values: HashMap<T, usize, S>,
    total_size: usize,
}

impl<T: Eq + Hash> MultiHashSet<T> {
    /// Constructs a new MultiHashSet. The underlying storage will use the
    /// default hasher algorithm, and use a default capacity.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set: MultiHashSet<String> = MultiHashSet::new();
    /// ```
    pub fn new() -> MultiHashSet<T> {
        MultiHashSet { 
            values: HashMap::new(),
            total_size: 0
        }
    }

    /// Constructs a new MultiHashSet. The underlying storage will use the
    /// default hasher algorithm, and be of the given capacity.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set: MultiHashSet<String> = MultiHashSet::with_capacity(10);
    /// assert!(set.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> MultiHashSet<T> {
        MultiHashSet {
            values: HashMap::with_capacity(capacity),
            total_size: 0
        }
    }
}

impl<T: Eq + Hash, S: BuildHasher> MultiHashSet<T, S> {
    /// Constructs a new MultiHashSet. The underlying storage will use the given
    /// hasher, and be of a default capacity.
    /// ```rust
    /// use std::collections::hash_map::RandomState;
    /// use multi_collections::MultiHashSet;
    /// let set: MultiHashSet<String> = MultiHashSet::with_hasher(RandomState::new());
    /// ```
    pub fn with_hasher(hash_builder: S) -> MultiHashSet<T, S> {
        MultiHashSet {
            values: HashMap::with_hasher(hash_builder),
            total_size: 0
        }
    }

    /// Constructs a new MultiHashSet. The underlying storage will use the given
    /// hasher and capacity.
    /// ```rust
    /// use std::collections::hash_map::RandomState;
    /// use multi_collections::MultiHashSet;
    /// let set: MultiHashSet<String> = MultiHashSet::with_capacity_and_hasher(10, RandomState::new());
    /// assert!(set.capacity() >= 10);
    /// ```
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> MultiHashSet<T, S> {
        MultiHashSet {
            values: HashMap::with_capacity_and_hasher(capacity, hash_builder),
            total_size: 0
        }
    }

    

    /// Returns a reference to the hasher used by the underlying storage.
    /// ```rust
    /// use std::collections::hash_map::RandomState;
    /// use multi_collections::MultiHashSet;
    /// let set: MultiHashSet<String> = MultiHashSet::with_hasher(RandomState::new());
    /// let hasher: &RandomState = set.hasher();
    /// ```
    pub fn hasher(&self) -> &S {
        self.values.hasher()
    }

    /// Returns the current capacity of the underlying storage.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set: MultiHashSet<String> = MultiHashSet::with_capacity(10);
    /// assert!(set.capacity() >= 10);
    /// ```
    pub fn capacity(&self) -> usize {
        self.values.capacity()
    }

    /// Instructs the underlying storage to reserve space for additional items.
    /// 
    /// # Panics
    /// Panics if the new allocation size overflows `usize`.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let mut set: MultiHashSet<String> = MultiHashSet::new();
    /// set.reserve(100);
    /// assert!(set.capacity() >= 100);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.values.reserve(additional)
    }

    /// Shrinks the capacity of the underlying storage as much as possible.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let mut set: MultiHashSet<i32> = [1, 2].iter().cloned().collect();
    /// set.reserve(100);
    /// assert!(set.capacity() >= 100);
    /// set.shrink_to_fit();
    /// assert!(set.capacity() >= 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.values.shrink_to_fit()
    }

    /// Returns an iterator over the items in the [`MultiHashMap`] in an
    /// arbitrary order. The iterator's type is `(&'a T. &'a usize)`. The first
    /// item in the type is the a reference to the item, while the second is a
    /// reference to the number of times the item exists in the
    /// [`MultiHashMap`]. The second element will never be zero.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set: MultiHashSet<&str> = ["alice", "alice", "bob"].iter().cloned().collect();
    /// // This will either print "alice has a count of 2" or "bob has a count of 1" in an arbitrary order.
    /// for (item, count) in set.iter() {
    ///   println!("{} has a count of {}", item, count)
    /// }
    /// ```
    pub fn iter(&self) -> HashMapIter<T, usize> {
        self.values.iter()
    }

    /// Returns an iterator over the sum of items in `self` and `other`. If an
    /// item exists in both sets, their counts are added together. If they exist
    /// in either, the count remains the same. The order is arbitrary and the
    /// iterator's type is `(&'a T, usize)`.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set1: MultiHashSet<&str> = ["alice", "alice"].iter().cloned().collect();
    /// let set2: MultiHashSet<&str> = ["alice", "bob"].iter().cloned().collect();
    /// // This will either print "alice has a count of 3" or "bob has a count of 1" in an arbitrary order.
    /// for (item, count) in set1.sum(&set2) {
    ///   println!("{} has a count of {}", item, count);
    /// }
    /// ```
    pub fn sum<'a, S2: 'a + BuildHasher>(&'a self, other: &'a MultiHashSet<T, S2>) -> SumIterator<'a, T, S, S2> {
        SumIterator::new(self, other)
    }

    /// Returns an iterator over the difference of items in `self` and `other`.
    /// If an item exists in `self` and `other`, the resultant count is the
    /// difference betweemn the count in `self` and the count in `other`. If
    /// the item's count in `self` is less than the count in `other`, the item
    /// is ignored. together. Items that exist in `other` and not `self` are
    /// ignored. The order is arbitrary and the iterator's type is
    /// `(&'a T, usize)`.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set1: MultiHashSet<&str> = ["alice", "alice"].iter().cloned().collect();
    /// let set2: MultiHashSet<&str> = ["alice", "bob"].iter().cloned().collect();
    /// // This will only print "alice has a count of 1".
    /// for (item, count) in set1.difference(&set2) {
    ///   println!("{} has a count of {}", item, count);
    /// }
    /// ```
    pub fn difference<'a, S2: 'a + BuildHasher>(&'a self, other: &'a MultiHashSet<T, S2>) -> DifferenceIterator<'a, T, S, S2> {
        DifferenceIterator::new(self, other)
    }

    /// Returns an iterator over the minimum of items in `self` and `other`. If
    /// an item exists in both sets, their counts are added together. If they exist
    /// in either, the count remains the same. The order is arbitrary and the
    /// iterator's type is `(&'a T, usize)`
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set1: MultiHashSet<&str> = ["alice", "alice"].iter().cloned().collect();
    /// let set2: MultiHashSet<&str> = ["alice", "bob"].iter().cloned().collect();
    /// // This will only print "alice has a count of 2".
    /// for (item, count) in set1.min(&set2) {
    ///   println!("{} has a count of {}", item, count);
    /// }
    /// ```
    pub fn min<'a, S2: 'a + BuildHasher>(&'a self, other: &'a MultiHashSet<T, S2>) -> MinIterator<'a, T, S, S2> {
        MinIterator::new(self, other)
    }

    /// Returns an iterator over the maximum of items in `self` and `other`. If
    /// an item exists in both sets, only the largest count is output by the
    /// iterator. If they exist in either, the count remains the same. The order
    /// is arbitrary and the iterator's type is `(&'a T, usize)`
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set1: MultiHashSet<&str> = ["alice", "alice"].iter().cloned().collect();
    /// let set2: MultiHashSet<&str> = ["alice", "bob"].iter().cloned().collect();
    /// // This will either print "alice has a count of 2" or "bob has a count of 1" in an arbitrary order.
    /// for (item, count) in set1.max(&set2) {
    ///   println!("{} has a count of {}", item, count);
    /// }
    /// ```
    pub fn max<'a, S2: 'a + BuildHasher>(&'a self, other: &'a MultiHashSet<T, S2>) -> MaxIterator<'a, T, S, S2> {
        MaxIterator::new(self, other)
    }
    
    /// Returns the number of distinct items in the MultiHashSet. Repeated items
    /// will only be counted once.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set: MultiHashSet<&str> = ["alice", "alice", "bob"].iter().cloned().collect();
    /// assert_eq!(set.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Returns the cumulative number of items in the MultiHashSet. Repeated
    /// items will be counted multiple times. This is never less than the `len`
    /// function's result.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set: MultiHashSet<&str> = ["alice", "alice", "bob"].iter().cloned().collect();
    /// assert_eq!(set.size(), 3);
    /// ```
    pub fn size(&self) -> usize {
        self.total_size
    }

    /// Returns whether there are items in the collection.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let mut set: MultiHashSet<&str> = ["alice", "alice"].iter().cloned().collect();
    /// assert!(!set.is_empty());
    /// set.remove_all("alice");
    /// assert!(set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Clears the set, returning all elements in an iterator.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let mut set: MultiHashSet<&str> = ["alice", "alice", "bob"].iter().cloned().collect();
    /// assert_eq!(set.len(), 2);
    /// assert_eq!(set.size(), 3);
    /// for _ in set.drain() {
    /// }
    /// assert_eq!(set.len(), 0);
    /// assert_eq!(set.size(), 0);
    /// ```
    pub fn drain(&mut self) -> HashMapDrain<T, usize> {
        self.total_size = 0;
        self.values.drain()
    }

    /// Clears the set.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let mut set: MultiHashSet<&str> = ["alice", "alice", "bob"].iter().cloned().collect();
    /// assert_eq!(set.len(), 2);
    /// assert_eq!(set.size(), 3);
    /// set.clear();
    /// assert_eq!(set.len(), 0);
    /// assert_eq!(set.size(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.total_size = 0;
        self.values.clear()
    }

    /// Returns whether at least one of an item is in the multiset.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set: MultiHashSet<&str> = ["alice", "alice", "bob"].iter().cloned().collect();
    /// assert!(set.contains("alice"));
    /// assert!(set.contains("bob"));
    /// assert!(!set.contains("charlie"));
    /// ```
    pub fn contains<Q: ?Sized>(&self, key: &Q) -> bool
        where T: Borrow<Q>,
              Q: Hash + Eq
    {
        self.get_count(key) >= 1
    }

    /// Returns the number of times the item exists in the multiset.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set: MultiHashSet<&str> = ["alice", "alice", "bob"].iter().cloned().collect();
    /// assert_eq!(set.get_count("alice"), 2);
    /// assert_eq!(set.get_count("bob"), 1);
    /// assert_eq!(set.get_count("charlie"), 0);
    /// ```
    pub fn get_count<Q: ?Sized>(&self, key: &Q) -> usize
        where T: Borrow<Q>,
              Q: Hash + Eq
    {
        *self.values.get(key).unwrap_or(&0)
    }

    /// Returns true if `self` contains no items in common with `other`.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set1: MultiHashSet<&str> = ["alice", "bob"].iter().cloned().collect();
    /// let set2: MultiHashSet<&str> = ["alfred", "bridget"].iter().cloned().collect();
    /// let set3: MultiHashSet<&str> = ["alice", "bridget", "eve"].iter().cloned().collect();
    /// assert!(set1.is_disjoint(&set2));
    /// assert!(!set1.is_disjoint(&set3));
    /// assert!(!set2.is_disjoint(&set3));
    /// ```
    pub fn is_disjoint(&self, other: &MultiHashSet<T, S>) -> bool {
        for  (item, _count) in self.iter() {
            if other.contains(&item) {
                return false;
            }
        }
        true
    }

    /// Returns true if `self` is a subset of `other`. `self` is a subset of
    /// `other` if every item in `self` exists in `other`. If an item occurs
    /// multiple times in `self` it must occur at least as many times in
    /// `other`.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set1: MultiHashSet<&str> = ["alice", "alice", "bob"].iter().cloned().collect();
    /// let set2: MultiHashSet<&str> = ["alice", "alice", "alice", "bob", "charlie"].iter().cloned().collect();
    /// assert!(set1.is_subset(&set2));
    /// ```
    pub fn is_subset(&self, other: &MultiHashSet<T, S>) -> bool {
        for (item, count) in self.iter() {
            let other_count = other.get_count(item);
            if *count > other_count {
                return false;
            }
        }
        true
    }

    /// Returns true if `self` is a superset of `other`. Every item in `self`
    /// must also exist at least as many times as it exists in `other`. 
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set1: MultiHashSet<&str> = ["alice", "alice", "bob"].iter().cloned().collect();
    /// let set2: MultiHashSet<&str> = ["alice", "alice", "alice", "bob", "charlie"].iter().cloned().collect();
    /// assert!(set2.is_superset(&set1));
    /// ```
    pub fn is_superset(&self, other: &MultiHashSet<T, S>) -> bool {
        other.is_subset(self)
    }

    /// Inserts an item multiple times into the multiset. Returns the number of
    /// times the item was in the multiset before insertion took place. If the
    /// item did not exist, this returns 0.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let mut set: MultiHashSet<&str> = MultiHashSet::new();
    /// assert_eq!(set.insert_multiple("alice", 1000), 0);
    /// assert_eq!(set.insert_multiple("alice", 1000), 1000);
    /// assert_eq!(set.get_count("alice"), 2000);
    /// ```
    pub fn insert_multiple(&mut self, value: T, count: usize) -> usize {
        self.total_size += count;
        match self.values.entry(value) {
            Entry::Occupied(o) => { let x = o.into_mut(); let result = *x; *x += count; result }
            Entry::Vacant(v) => {if count > 0 { v.insert(count); } 0 }
        }
    }

    /// Inserts an item in the multiset. This returns the number of times the
    /// item was in the multiset before the insertion took place. If the item
    /// did not exist, this returns 0.
    /// # Notable Difference
    /// The standard library's HashSet returns true if the item was inserted in
    /// the set. Insertions always (barring panics) succeed in a multiset so a
    /// value of true would always be returned. The number of items that were
    /// previously in the multiset was chosen as a more useful replacement.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let mut set: MultiHashSet<&str> = MultiHashSet::new();
    /// assert_eq!(set.insert("alice"), 0);
    /// assert_eq!(set.insert("alice"), 1);
    /// assert_eq!(set.get_count("alice"), 2);
    /// ```
    pub fn insert(&mut self, value: T) -> usize {
        self.insert_multiple(value, 1)
    }

    /// Removes all occurrences of an item from the multiset. If the item exists
    /// in the multiset, this will decrease the `len` by 1.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let mut set: MultiHashSet<&str> = MultiHashSet::new();
    /// set.insert_multiple("alice", 1000);
    /// assert_eq!(set.get_count("alice"), 1000);
    /// assert_eq!(set.len(), 1); 
    /// set.remove_all("alice");
    /// assert_eq!(set.get_count("alice"), 0);
    /// assert_eq!(set.len(), 0);
    /// ```
    pub fn remove_all<Q: ?Sized>(&mut self, value: &Q) -> usize
        where T: Borrow<Q>,
              Q: Hash + Eq
    {
        let previous_count = self.get_count(value);
        if previous_count > 0 {
            self.values.remove(value);
            self.total_size -= previous_count;
        }
        previous_count
    }

    /// Removes an item multiple times from the multiset. If an item's count
    /// drops to 0 (or lower), the item is removed from the multiset.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let mut set: MultiHashSet<&str> = MultiHashSet::new();
    /// set.insert_multiple("alice", 1000);
    /// assert_eq!(set.get_count("alice"), 1000);
    /// assert_eq!(set.len(), 1); 
    /// set.remove_multiple("alice", 500);
    /// assert_eq!(set.len(), 1);
    /// assert_eq!(set.get_count("alice"), 500);
    /// set.remove_multiple("alice", 9999);
    /// assert_eq!(set.get_count("alice"), 0);
    /// assert_eq!(set.len(), 0);
    /// ```
    pub fn remove_multiple<Q: ?Sized>(&mut self, value: &Q, count: usize) -> usize
        where T: Borrow<Q>,
              Q: Hash + Eq
    {
        let previous_count = self.get_count(value);
        if previous_count > 0 {
            // Item exists in the multiset
            if previous_count <= count {
                self.values.remove(value);
                self.total_size -= previous_count;
            } else {
                *self.values.get_mut(value).unwrap() -= count;
                self.total_size -= count;
            }
        }
        previous_count
    }

    /// Removes an occurrence of an item from the multiset. If an item's count
    /// drops to 0, the item is removed from the multiset.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let mut set: MultiHashSet<&str> = MultiHashSet::new();
    /// set.insert_multiple("alice", 2);
    /// assert_eq!(set.get_count("alice"), 2);
    /// assert_eq!(set.len(), 1);
    /// set.remove("alice");
    /// assert_eq!(set.get_count("alice"), 1);
    /// assert_eq!(set.len(), 1); 
    /// set.remove("alice");
    /// assert_eq!(set.get_count("alice"), 0);
    /// assert_eq!(set.len(), 0);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, value: &Q) -> usize 
        where T: Borrow<Q>,
              Q: Hash + Eq
    {
        self.remove_multiple(value, 1)
    }

    /// Retains only the elements specified by the predicate.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let mut set: MultiHashSet<&str> = MultiHashSet::new();
    /// set.insert_multiple("alice", 5);
    /// set.insert_multiple("bob", 4);
    /// set.insert_multiple("charlie", 3);
    /// set.insert_multiple("dennis", 2);
    /// assert_eq!(set.size(), 14);
    /// assert_eq!(set.len(), 4);
    /// set.retain(|v, c| v.len() % 2 == 1);
    /// assert_eq!(set.get_count("alice"), 5);
    /// assert_eq!(set.get_count("bob"), 4);
    /// assert_eq!(set.get_count("charlie"), 3);
    /// assert_eq!(set.get_count("dennis"), 0);
    /// assert_eq!(set.size(), 12);
    /// assert_eq!(set.len(), 3);
    /// ```
    pub fn retain<F>(&mut self, mut f: F) 
        where F: FnMut(&T, &usize) -> bool
    {
        let mut total_removed = 0;
        {
            let total_removed_ref = &mut total_removed;
            let new_f = |k: &T, v: &mut usize| {
                if !f(k, v) {
                    *total_removed_ref += *v;
                    false
                } else {
                    true
                }
            };
            self.values.retain(new_f);
        }
        self.total_size -= total_removed;
    }

    /// Outputs each item in the multiset. If the item is in the multiset more
    /// than once, this will output the item once for each entry. It is
    /// guaranteed that if an item exists multiple times, then each occurrence
    /// of the item in the resulting iterator will be consecutive.
    /// ```rust
    /// use multi_collections::MultiHashSet;
    /// let set: MultiHashSet<&str> = ["alice", "alice", "bob"].iter().cloned().collect();
    /// // This will either print "alice,alice,bob," or "bob,alice,alice"
    /// for item in set.items() {
    ///   print!("{},", item)
    /// }
    /// ```
    pub fn items(&self) -> ItemIterator<T> {
        ItemIterator::new(self)
    }
}

impl<T, S> PartialEq for MultiHashSet<T, S>
    where T: Eq + Hash,
          S: BuildHasher
{
    fn eq(&self, other: &MultiHashSet<T, S>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter().all(|(key, count)| other.get_count(key) == *count)
    }
}

impl<T, S> Eq for MultiHashSet<T, S>
    where T: Eq + Hash,
          S: BuildHasher
{
}

impl<T, S> Default for MultiHashSet<T, S>
    where T: Eq + Hash,
          S: BuildHasher + Default
{
    fn default() -> Self {
        MultiHashSet::with_hasher(Default::default())
    }
}

impl<T, S> FromIterator<T> for MultiHashSet<T, S>
    where T: Eq + Hash,
          S: BuildHasher + Default
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> MultiHashSet<T, S> {
        let mut set = MultiHashSet::with_hasher(Default::default());
        set.extend(iter);
        set
    }
}

impl<T, S> FromIterator<(T, usize)> for MultiHashSet<T, S>
    where T: Eq + Hash,
          S: BuildHasher + Default
{
    fn from_iter<I: IntoIterator<Item = (T, usize)>>(iter: I) -> MultiHashSet<T, S> {
        let mut set = MultiHashSet::with_hasher(Default::default());
        set.extend(iter);
        set
    }
}


impl<'a, T, S> FromIterator<(&'a T, usize)> for MultiHashSet<T, S>
    where T: 'a + Eq + Hash + Clone,
          S: BuildHasher + Default
{
    fn from_iter<I: IntoIterator<Item = (&'a T, usize)>>(iter: I) -> MultiHashSet<T, S> {
        let mut set = MultiHashSet::with_hasher(Default::default());
        set.extend(iter);
        set
    }
}

impl<T, S> Extend<T> for MultiHashSet<T, S>
    where T: Eq + Hash,
          S: BuildHasher
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            self.insert(item);
        }
    }
}

impl<'a, T, S> Extend<&'a T> for MultiHashSet<T, S>
    where T: 'a + Eq + Hash + Copy,
          S: BuildHasher
{
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned())
    }
}

impl<T, S> Extend<(T, usize)> for MultiHashSet<T, S>
    where T: Eq + Hash,
          S: BuildHasher
{
    fn extend<I: IntoIterator<Item = (T, usize)>>(&mut self, iter: I) {
        for (item, count) in iter {
            self.insert_multiple(item, count);
        }
    }
}

impl<'a, T, S> Extend<(&'a T, usize)> for MultiHashSet<T, S>
    where T: 'a + Eq + Hash + Clone,
          S: BuildHasher
{
    fn extend<I: IntoIterator<Item = (&'a T, usize)>>(&mut self, iter: I) {
        self.extend(iter.into_iter().map(|(i, c)| (i.clone(), c)))
    }
}

impl<'a, 'b, T, S> Add<&'b MultiHashSet<T, S>> for &'a MultiHashSet<T, S>
    where T: Eq + Hash + Clone,
          S: BuildHasher + Default
{
    type Output = MultiHashSet<T, S>;

    fn add(self, rhs: &MultiHashSet<T, S>) -> MultiHashSet<T, S> {
        self.sum(rhs).collect()
    }
}

impl<'a, 'b, T, S> Sub<&'b MultiHashSet<T, S>> for &'a MultiHashSet<T, S>
    where T: Eq + Hash + Clone,
          S: BuildHasher + Default
{
    type Output = MultiHashSet<T, S>;

    fn sub(self, rhs: &MultiHashSet<T, S>) -> MultiHashSet<T, S> {
        self.difference(rhs).collect()
    }
}

#[derive(Clone, Debug)]
pub struct SumIterator<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> {
    self_iterator: HashMapIter<'a, T, usize>,
    other_iterator: HashMapIter<'a, T, usize>,
    self_set: &'a MultiHashSet<T, S1>,
    other_set: &'a MultiHashSet<T, S2>,
    self_iterator_consumed: bool,
}

impl<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> SumIterator<'a, T, S1, S2> {
    pub fn new(self_set: &'a MultiHashSet<T, S1>, other_set: &'a MultiHashSet<T, S2>) -> SumIterator<'a, T, S1, S2> {
        SumIterator {
            self_iterator: self_set.iter(),
            other_iterator: other_set.iter(),
            self_set: self_set,
            other_set: other_set,
            self_iterator_consumed: false
        }
    }
}

impl<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> Iterator for SumIterator<'a, T, S1, S2> {
    type Item = (&'a T, usize);

    fn next(&mut self) -> Option<(&'a T, usize)> {
        if !self.self_iterator_consumed {
            loop {
                if let Some((item, count)) = self.self_iterator.next() {
                    let other_count = self.other_set.get_count(item);
                    return Some((item, *count + other_count));
                } else {
                    self.self_iterator_consumed = true;
                    break;
                }
            }
        }

        loop {
            let (item, count) = self.other_iterator.next()?;
            if !self.self_set.contains(item) {
                return Some((item, *count));
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper_self) = self.self_iterator.size_hint();
        let (_, upper_other) = self.other_iterator.size_hint();
        if upper_self.is_some() && upper_other.is_some() {
            (0, Some(upper_self.unwrap() + upper_other.unwrap()))
        } else {
            (0, None)
        }
    }
}

impl<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> FusedIterator for SumIterator<'a, T, S1, S2> {
}

#[derive(Clone, Debug)]
pub struct DifferenceIterator<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> {
    self_iterator: HashMapIter<'a, T, usize>,
    other_set: &'a MultiHashSet<T, S2>,
    self_hash_type: PhantomData<S1>
}

impl<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> DifferenceIterator<'a, T, S1, S2> {
    pub fn new(self_set: &'a MultiHashSet<T, S1>, other_set: &'a MultiHashSet<T, S2>) -> DifferenceIterator<'a, T, S1, S2> {
        DifferenceIterator {
            self_iterator: self_set.iter(),
            other_set: other_set,
            self_hash_type: PhantomData,
        }
    }
}

impl<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> Iterator for DifferenceIterator<'a, T, S1, S2> {
    type Item = (&'a T, usize);

    fn next(&mut self) -> Option<(&'a T, usize)> {
        loop {
            let (item, count) = self.self_iterator.next()?;
            let other_count = self.other_set.get_count(item);
            if other_count < *count {
                return Some((item, count - other_count));
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper_self) = self.self_iterator.size_hint();
        (0, upper_self)
    }
}

impl<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> FusedIterator for DifferenceIterator<'a, T, S1, S2> {
}

#[derive(Clone, Debug)]
pub struct MaxIterator<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> {
    self_iterator: HashMapIter<'a, T, usize>,
    other_iterator: HashMapIter<'a, T, usize>,
    self_set: &'a MultiHashSet<T, S1>,
    other_set: &'a MultiHashSet<T, S2>,
    self_iterator_consumed: bool,
}

impl<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> MaxIterator<'a, T, S1, S2> {
    pub fn new(self_set: &'a MultiHashSet<T, S1>, other_set: &'a MultiHashSet<T, S2>) -> MaxIterator<'a, T, S1, S2> {
        MaxIterator {
            self_iterator: self_set.iter(),
            other_iterator: other_set.iter(),
            self_set: self_set,
            other_set: other_set,
            self_iterator_consumed: false
        }
    }
}

impl<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> Iterator for MaxIterator<'a, T, S1, S2> {
    type Item = (&'a T, usize);

    fn next(&mut self) -> Option<(&'a T, usize)> {
        if !self.self_iterator_consumed {
            loop {
                if let Some((item, count)) = self.self_iterator.next() {
                    let other_count = self.other_set.get_count(item);
                    return Some((item, max(*count, other_count)));
                } else {
                    self.self_iterator_consumed = true;
                    break;
                }
            }
        }

        loop {
            let (item, count) = self.other_iterator.next()?;
            if !self.self_set.contains(item) {
                return Some((item, *count));
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper_self) = self.self_iterator.size_hint();
        let (_, upper_other) = self.other_iterator.size_hint();
        if upper_self.is_some() && upper_other.is_some() {
            (0, Some(upper_self.unwrap() + upper_other.unwrap()))
        } else {
            (0, None)
        }
    }
}

impl<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> FusedIterator for MaxIterator<'a, T, S1, S2> {
}

#[derive(Clone, Debug)]
pub struct MinIterator<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> {
    self_iterator: HashMapIter<'a, T, usize>,
    other_set: &'a MultiHashSet<T, S2>,
    self_hash_type: PhantomData<S1>,
}

impl<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> MinIterator<'a, T, S1, S2> {
    pub fn new(self_set: &'a MultiHashSet<T, S1>, other_set: &'a MultiHashSet<T, S2>) -> MinIterator<'a, T, S1, S2> {
        MinIterator {
            self_iterator: self_set.iter(),
            other_set: other_set,
            self_hash_type: PhantomData
        }
    }
}

impl<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> Iterator for MinIterator<'a, T, S1, S2> {
    type Item = (&'a T, usize);

    fn next(&mut self) -> Option<(&'a T, usize)> {
        loop {
            let (item, count) = self.self_iterator.next()?;
            let other_count = self.other_set.get_count(item);
            if other_count != 0 {
                return Some((item, min(other_count, *count)));
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper_self) = self.self_iterator.size_hint();
        (0, upper_self)
    }
}

impl<'a, T: 'a + Hash + Eq, S1: 'a + BuildHasher, S2: 'a + BuildHasher> FusedIterator for MinIterator<'a, T, S1, S2> {
}


#[derive(Clone, Debug)]
pub struct ItemIterator<'a, T: 'a + Hash + Eq> {
    inner_iterator: HashMapIter<'a, T, usize>,
    last_value: Option<&'a T>,
    last_values_left: usize,
    total_size: usize,
    times_iterated: usize,
}

impl<'a, T: 'a + Hash + Eq, > ItemIterator<'a, T> {
    pub fn new<S: 'a + BuildHasher>(self_set: &'a MultiHashSet<T, S>) -> ItemIterator<'a, T> {
        ItemIterator {
            inner_iterator: self_set.iter(),
            last_value: None,
            last_values_left: 0,
            total_size: self_set.size(),
            times_iterated: 0,
        }
    }
}

impl<'a, T: 'a + Hash + Eq> Iterator for ItemIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let should_call_iterator = if let Some(_value) = self.last_value {
            // Only refresh if the available items left is 0
            self.last_values_left == 0
        } else {
            // There is no entry in the iterator's value - we need to refresh if there is
            true
        };

        if should_call_iterator {
            if let Some((value, count)) = self.inner_iterator.next() {
                self.last_value = Some(value);
                self.last_values_left = *count;
            } else {
                self.last_value = None
            }
        }

        if let Some(_value) = self.last_value {
            self.times_iterated += 1;
            self.last_values_left -= 1;
            self.last_value
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.total_size))
    }
}

impl<'a, T: 'a + Hash + Eq> FusedIterator for ItemIterator<'a, T> {
}


#[cfg(test)]
mod tests {
    use super::MultiHashSet;

    #[test]
    fn test_new_capacity_0() {
        let hashset: MultiHashSet<String> = MultiHashSet::new();
        assert_eq!(hashset.capacity(), 0);
        assert_eq!(hashset.len(), 0);
    }

    #[test]
    fn test_insertions_and_deletions() {
        let mut hashset: MultiHashSet<String> = MultiHashSet::new();
        assert_eq!(hashset.get_count("missing"), 0);
        hashset.insert("abcd".to_string());
        assert_eq!(hashset.len(), 1);
        assert_eq!(hashset.get_count("abcd"), 1);
        assert_eq!(hashset.len(), 1);
        assert_eq!(hashset.get_count("missing"), 0);
        hashset.insert("abcd".to_string());
        assert_eq!(hashset.len(), 1);
        assert_eq!(hashset.size(), 2);
        assert_eq!(hashset.get_count("abcd"), 2);
        hashset.remove("abcd");
        assert_eq!(hashset.len(), 1);
        assert_eq!(hashset.get_count("abcd"), 1);
        hashset.remove("abcd");
        assert_eq!(hashset.len(), 0);
        assert_eq!(hashset.get_count("abcd"), 0);
    }

    #[test]
    fn test_sum() {
        let set1: MultiHashSet<&str> = ["alice", "alice"].iter().cloned().collect();
        let set2: MultiHashSet<&str> = ["alice", "bob"].iter().cloned().collect();
        for (_item, _count) in set1.sum(&set2) {
        }
    }

    #[test]
    fn test_difference() {
        let set1: MultiHashSet<&str> = ["alice", "alice"].iter().cloned().collect();
        let set2: MultiHashSet<&str> = ["alice", "bob"].iter().cloned().collect();
        for (_item, _count) in set1.difference(&set2) {
        }
    }

    #[test]
    fn test_max() {
        let set1: MultiHashSet<&str> = ["alice", "alice"].iter().cloned().collect();
        let set2: MultiHashSet<&str> = ["alice", "bob"].iter().cloned().collect();
        for (_item, _count) in set1.max(&set2) {
        }
    }

    #[test]
    fn test_min() {
        let set1: MultiHashSet<&str> = ["alice", "alice"].iter().cloned().collect();
        let set2: MultiHashSet<&str> = ["alice", "bob"].iter().cloned().collect();
        for (_item, _count) in set1.min(&set2) {
        }
    }

    #[test]
    fn test_collect() {
        let set: MultiHashSet<&str> = [("alice", 2), ("bob", 4)].iter().cloned().collect();
        assert_eq!(set.len(), 2);
        assert_eq!(set.size(), 6);
    }
}