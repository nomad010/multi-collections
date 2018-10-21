use std::collections::{HashMap, hash_map::{Entry, Iter as HashMapIter, RandomState}};
use std::hash::{Hash, BuildHasher};
use std::iter::{ExactSizeIterator, FusedIterator};
use std::borrow::Borrow;


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

    pub fn iter(&self) -> Iter<T> {
        Iter::new(self.values.iter(), self.total_size)
    }

    /*
    Iterator stuff here

    pub fn difference<'a>(
    &'a self, 
    other: &'a HashSet<T, S>
) -> Difference<'a, T, S>

pub fn symmetric_difference<'a>(
    &'a self, 
    other: &'a HashSet<T, S>
) -> SymmetricDifference<'a, T, S>

pub fn intersection<'a>(
    &'a self, 
    other: &'a HashSet<T, S>
) -> Intersection<'a, T, S>

pub fn union<'a>(&'a self, other: &'a HashSet<T, S>) -> Union<'a, T, S>
    */

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
        match self.values.entry(value) {
            Entry::Occupied(o) => { let x = o.into_mut(); *x += 1; false }
            Entry::Vacant(v) => {v.insert(0); true }
        }
    }

    pub fn remove<Q: ?Sized>(&mut self, value: &Q) -> bool 
        where T: Borrow<Q>,
              Q: Hash + Eq
    {
        let value = self.values.get(value);

        match value {
            Some(1) => { true },
            Some(x) => { true },
            None => { false }
        }
        /*
        if self.values.contains_key(value) {
            self.values.get_mut()
            true
        } else {
            false
        }
        match self.values.entry(value.borrow()) {
            Entry::Occupied(o) => { 
                let x = o.into_mut();
                *x -= 1;
                if *x == 0 {
                    o.remove_entry();
                }
                true
            },
            Entry::Vacant(v) => { false }
        }
        */
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
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
    type Item = &'a T;

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

/*
#[derive(Clone, Debug)]
struct Difference<'a, T: 'a + Hash + Eq, S: 'a + BuildHasher> {
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
*/