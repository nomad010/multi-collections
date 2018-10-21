use std::collections::{HashMap, hash_map::{Iter as HashMapIter, RandomState}};
use std::hash::{Hash, BuildHasher};
use std::iter::{ExactSizeIterator, FusedIterator};


#[derive(Clone)]
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
}

impl<'a, T: 'a> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        self.total_size - self.times_iterated
    }
}

impl<'a, T: 'a> FusedIterator for Iter<'a, T> {
}


#[derive(Debug)]
struct Difference<'a, T: 'a, S: 'a> {
    iter: Iter<'a, T>,
    // the second set
    other: &'a HashMap<T, usize, S>,
}