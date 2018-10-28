use std::collections::{HashMap, hash_map::{Entry, Iter as HashMapIter, Drain as HashMapDrain, RandomState}};
use std::hash::{Hash, BuildHasher};
use std::iter::FusedIterator;
use std::borrow::Borrow;
use std::ops::Index;
use std::cmp::{max, min};
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
/// and [`MultiHashSet`].
/// Examples:
#[derive(Clone, Debug)]
pub struct MultiHashSet<T: Eq + Hash, S : BuildHasher = RandomState> {
    values: HashMap<T, usize, S>,
    total_size: usize,
}

impl<T: Eq + Hash> MultiHashSet<T> {
    /// Constructs a new MultiHashSet. The underlying storage will use the
    /// default hasher algorithm, and use a default capacity.
    pub fn new() -> MultiHashSet<T> {
        MultiHashSet { 
            values: HashMap::new(),
            total_size: 0
        }
    }

    /// Constructs a new MultiHashSet. The underlying storage will use the
    /// default hasher algorithm, and be of the given capacity.
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
    pub fn with_hasher(hash_builder: S) -> MultiHashSet<T, S> {
        MultiHashSet {
            values: HashMap::with_hasher(hash_builder),
            total_size: 0
        }
    }

    /// Constructs a new MultiHashSet. The underlying storage will use the given
    /// hasher and capacity.
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> MultiHashSet<T, S> {
        MultiHashSet {
            values: HashMap::with_capacity_and_hasher(capacity, hash_builder),
            total_size: 0
        }
    }

    /// Returns a reference to the hasher used by the underlying storage.
    pub fn hasher(&self) -> &S {
        self.values.hasher()
    }

    /// Returns the current capacity of the underlying storage.
    pub fn capacity(&self) -> usize {
        self.values.capacity()
    }

    /// Instructs the underlying storage to reserve space for additional items.
    /// 
    /// # Panics
    /// Panics if the new allocation size overflows `usize`.
    pub fn reserve(&mut self, additional: usize) {
        self.values.reserve(additional)
    }

    /// Shrinks the capacity of the underlying storage as much as possible.
    pub fn shrink_to_fit(&mut self) {
        self.values.shrink_to_fit()
    }

    /// Returns an iterator over the items in the [`MultiHashMap`] in an
    /// arbitrary order. The iterator's type is `(&'a T. &'a usize)`. The first
    /// item in the type is the a reference to the item, while the second is a
    /// reference to the number of times the item exists in the
    /// [`MultiHashMap`]. The second element will never be zero.
    pub fn iter(&self) -> HashMapIter<T, usize> {
        self.values.iter()
    }

    /// Returns an iterator over the sum of items in `self` and `other`. If an
    /// item exists in both sets, their counts are added together. If they exist
    /// in either, the count remains the same. The order is arbitrary and the
    /// iterator's type is `(&'a T, usize)`.
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
    pub fn difference<'a, S2: 'a + BuildHasher>(&'a self, other: &'a MultiHashSet<T, S2>) -> DifferenceIterator<'a, T, S, S2> {
        DifferenceIterator::new(self, other)
    }

    /// Returns an iterator over the minimum of items in `self` and `other`. If
    /// an item exists in both sets, their counts are added together. If they exist
    /// in either, the count remains the same. The order is arbitrary and the
    /// iterator's type is `(&'a T, usize)`
    pub fn min<'a, S2: 'a + BuildHasher>(&'a self, other: &'a MultiHashSet<T, S2>) -> MinIterator<'a, T, S, S2> {
        MinIterator::new(self, other)
    }

    pub fn max<'a, S2: 'a + BuildHasher>(&'a self, other: &'a MultiHashSet<T, S2>) -> MaxIterator<'a, T, S, S2> {
        MaxIterator::new(self, other)
    }

    pub fn len(&self) -> usize {
        self.total_size
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    pub fn drain(&mut self) -> HashMapDrain<T, usize> {
        self.values.drain()
    }

    pub fn clear(&mut self) {
        self.total_size = 0;
        self.values.clear()
    }

    pub fn contains<Q: ?Sized>(&self, key: &Q) -> bool
        where T: Borrow<Q>,
              Q: Hash + Eq
    {
        self.values.contains_key(key)
    }

    pub fn get_count<Q: ?Sized>(&self, key: &Q) -> usize
        where T: Borrow<Q>,
              Q: Hash + Eq
    {
        *self.values.get(key).unwrap_or(&0)
    }

    pub fn is_disjoint(&self, other: &MultiHashSet<T, S>) -> bool {
        for  (item, _count) in self.iter() {
            if other.contains(&item) {
                return false;
            }
        }
        true
    }

    pub fn is_strict_subset(&self, other: &MultiHashSet<T, S>) -> bool {
        for (item, count) in self.iter() {
            let other_count = other.get_count(item);
            if *count >= other_count {
                return false;
            }
        }
        true
    }

    pub fn is_subset(&self, other: &MultiHashSet<T, S>) -> bool {
        for (item, count) in self.iter() {
            let other_count = other.get_count(item);
            if *count > other_count {
                return false;
            }
        }
        true
    }

    pub fn is_superset(&self, other: &MultiHashSet<T, S>) -> bool {
        other.is_subset(self)
    }

    pub fn insert(&mut self, value: T) -> bool {
        self.total_size += 1;
        match self.values.entry(value) {
            Entry::Occupied(o) => { let x = o.into_mut(); *x += 1; false }
            Entry::Vacant(v) => {v.insert(1); true }
        }
    }

    pub fn remove<Q: ?Sized>(&mut self, value: &Q) -> bool 
        where T: Borrow<Q>,
              Q: Hash + Eq
    {
        if self.values.contains_key(value) {
            if self.values.get(value) == Some(&1) {
                self.values.remove(value);
            } else {
                *self.values.get_mut(value).unwrap() -= 1;
            }
            self.total_size -= 1;
            true
        } else {
            false
        }
    }

    pub fn retain<F>(&mut self, mut f: F) 
        where F: FnMut(&T, &mut usize) -> bool
    {
        let total_removed = &mut 0;
        let new_f = |k: &T, v: &mut usize| {
            if !f(k, v) {
                *total_removed += *v;
                false
            } else {
                true
            }
        };
        self.values.retain(new_f)
    }
}

impl<'a, K: Eq + Hash + Borrow<Q>, Q: ?Sized + Eq + Hash, S: BuildHasher> Index<&'a Q> for MultiHashSet<K, S> {
    type Output = usize;

    fn index(&self, key: &Q) -> &usize {
        self.values.get(key).unwrap_or(&0)
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
            if other_count > *count {
                return Some((item, other_count - count));
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
        assert_eq!(hashset.len(), 2);
        assert_eq!(hashset.get_count("abcd"), 2);
        hashset.remove("abcd");
        assert_eq!(hashset.len(), 1);
        assert_eq!(hashset.get_count("abcd"), 1);
        hashset.remove("abcd");
        assert_eq!(hashset.len(), 0);
        assert_eq!(hashset.get_count("abcd"), 0);
    }
}