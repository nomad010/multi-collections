use std::collections::{HashMap, hash_map::{Entry, Iter as HashMapIter, Drain as HashMapDrain, RandomState}};
use std::hash::{Hash, BuildHasher};
use std::iter::{Chain, ExactSizeIterator, FusedIterator};
use std::borrow::Borrow;
use std::ops::Index;


#[derive(Clone, Debug)]
pub struct MultiHashSet<T: Eq + Hash, S : BuildHasher = RandomState> {
    values: HashMap<T, usize, S>,
    total_size: usize,
}

impl<T: Eq + Hash> MultiHashSet<T> {
    pub fn new() -> MultiHashSet<T> {
        MultiHashSet { 
            values: HashMap::new(),
            total_size: 0
        }
    }

    pub fn with_capacity(capacity: usize) -> MultiHashSet<T> {
        MultiHashSet {
            values: HashMap::with_capacity(capacity),
            total_size: 0
        }
    }
}

impl<T: Eq + Hash, S: BuildHasher> MultiHashSet<T, S> {
    pub fn with_hasher(hash_builder: S) -> MultiHashSet<T, S> {
        MultiHashSet {
            values: HashMap::with_hasher(hash_builder),
            total_size: 0
        }
    }

    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> MultiHashSet<T, S> {
        MultiHashSet {
            values: HashMap::with_capacity_and_hasher(capacity, hash_builder),
            total_size: 0
        }
    }

    pub fn hasher(&self) -> &S {
        &self.values.hasher()
    }

    pub fn capacity(&self) -> usize {
        self.values.capacity()
    }

    pub fn reserve(&mut self, additional: usize) {
        self.values.reserve(additional)
    }

    pub fn shrink_to_fit(&mut self) {
        self.values.shrink_to_fit()
    }

    pub fn iter(&self) -> HashMapIter<T, usize> {
        self.values.iter()
    }

    pub fn difference<'a>(&'a self, other: &'a MultiHashSet<T, S>) -> Difference<'a, T, S> {
        Difference {
            iter: self.iter(),
            other: other
        }
    }

    pub fn symmetric_difference<'a>(&'a self, other: &'a MultiHashSet<T, S>) -> SymmetricDifference<'a, T, S> {
        SymmetricDifference {
            iter: self.difference(other).chain(other.difference(self)),
        }
    }

    pub fn intersection<'a>(&'a self, other: &'a MultiHashSet<T, S>) -> Intersection<'a, T, S> {
        Intersection {
            iter: self.iter(),
            other: other
        }
    }

    pub fn union<'a>(&'a self, other: &'a MultiHashSet<T, S>) -> Union<'a, T, S> {
        Union {
            iter: self.iter().chain(other.difference(self))
        }
    }

    pub fn len(&self) -> usize {
        self.total_size
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /*
    pub fn drain(&mut self) -> Drain<T>
    */

    pub fn clear(&mut self) {
        self.total_size = 0;
        self.values.clear()
    }

    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
        where T: Borrow<Q>,
              Q: Hash + Eq
    {
        self.values.contains_key(value)
    }

    pub fn get_count<Q: ?Sized>(&self, value: &Q) -> usize
        where T: Borrow<Q>,
              Q: Hash + Eq
    {
        *self.values.get(value).unwrap_or(&0)
    }

    pub fn is_disjoint(&self, other: &MultiHashSet<T, S>) -> bool {
        for ref item in self.iter() {
            if other.contains(&item) {
                return false;
            }
        }
        true
    }

    pub fn is_subset(&self, other: &MultiHashSet<T, S>) -> bool {
        for ref item in self.iter() {
            if !other.contains(&item) {
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
pub struct Iter<'a, T: 'a> {
    internal_iterator: HashMapIter<'a, T, usize>,
    value_left: usize,
    value: Option<&'a T>,
    total_size: usize,
    times_iterated: usize,
}

impl<'a, T: 'a> Iter<'a, T> {
    fn new(internal_iterator: HashMapIter<'a, T, usize>, total_size: usize) -> Iter<'a, T> {
        if let Some((value, count)) = internal_iterator.clone().next() {
            Iter {
                internal_iterator: internal_iterator,
                value_left: *count,
                value: Some(value),
                total_size: total_size,
                times_iterated: 0,
            }
        } else {
            Iter {
                internal_iterator: internal_iterator,
                value_left: 0,
                value: None,
                total_size: total_size,
                times_iterated: 0,
            }
        }
    }
}

impl<'a, T: 'a> Iterator for Iter<'a, T> {
    type Item = (&'a T, &'a usize);

    fn next(&mut self) -> Option<&'a T> {
        if self.value.is_none() {
            None
        } else {
            if self.value_left == 0 {
                if let Some((value, count)) = self.internal_iterator.next() {
                    self.value = Some(value);
                    self.value_left = *count;
                    self.times_iterated += 1;
                    self.value
                } else {
                    self.value = None;
                    self.value_left = 0;
                    None
                }
            } else {
                self.value_left -= 1;
                self.times_iterated += 1;
                self.value
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.len()))
    }
}

impl<'a, T: 'a> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        self.total_size - self.times_iterated
    }
}

impl<'a, T: 'a> FusedIterator for Iter<'a, T> {
}


#[derive(Clone, Debug)]
pub struct Difference<'a, T: 'a + Hash + Eq, S: 'a + BuildHasher> {
    iter: Iter<'a, T>,
    // the second set
    other: &'a MultiHashSet<T, S>,
}

impl<'a, T: Eq + Hash, S: BuildHasher> Iterator for Difference<'a, T, S> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            let elt = self.iter.next()?;
            if !self.other.contains(elt) {
                return Some(elt);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper)
    }
}

impl<'a, T: Eq + Hash, S: BuildHasher> FusedIterator for Difference<'a, T, S> {
}

#[derive(Clone, Debug)]
pub struct SymmetricDifference<'a, T: 'a + Eq + Hash, S: 'a + BuildHasher> {
    iter: Chain<Difference<'a, T, S>, Difference<'a, T, S>>,
}

impl<'a, T: Eq + Hash, S: BuildHasher> Iterator for SymmetricDifference<'a, T, S> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, T: Eq + Hash, S: BuildHasher> FusedIterator for SymmetricDifference<'a, T, S> {
}

#[derive(Clone, Debug)]
pub struct Intersection<'a, T: 'a + Hash + Eq, S: 'a + BuildHasher> {
    iter: Iter<(&'a T, &'a usize)>,
    // the second set
    other: &'a MultiHashSet<T, S>,
}

impl<'a, T: Eq + Hash, S: BuildHasher> Iterator for Intersection<'a, T, S> {
    type Item = (&'a T, &'a usize);

    fn next(&mut self) -> Option<&'a T> {
        loop {
            let elt = self.iter.next()?;
            if self.other.contains(elt) {
                return Some(elt);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper)
    }
}

impl<'a, T: Eq + Hash, S: BuildHasher> FusedIterator for Intersection<'a, T, S> {
}

#[derive(Clone, Debug)]
pub struct Union<'a, T: 'a + Eq + Hash, S: 'a + BuildHasher> {
    iter: Chain<Iter<'a, T>, Difference<'a, T, S>>,
}

impl<'a, T: Eq + Hash, S: BuildHasher> Iterator for Union<'a, T, S> {
    type Item = (&'a T, &'a usize);

    fn next(&mut self) -> Option<(&'a T, &'a usize)> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, T: Eq + Hash, S: BuildHasher> FusedIterator for Union<'a, T, S> {
}

/*
redo
#[derive(Clone, Debug)]
pub struct Drain<'a, T: 'a + Eq + Hash> {
    iter: HashMapDrain<'a, T, usize>,
}

impl<'a, T: Eq + Hash> Iterator for Drain<'a, T> {
    type Item = &'a (T, usize);

    fn next(&mut self) -> Option<&'a (T, usize)> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, T: 'a + Eq + Hash> ExactSizeIterator for Drain<'a, T> {
    fn len(&self) -> usize {
        self.iter. - self.times_iterated
    }
}

impl<'a, T: Eq + Hash> FusedIterator for Drain<'a, T> {
}
*/

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