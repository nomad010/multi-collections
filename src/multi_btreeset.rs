use std::collections::{BTreeMap};
use std::hash::{Hash, BuildHasher};
use std::iter::{FromIterator, FusedIterator};
use std::borrow::Borrow;
use std::cmp::{max, min};
use std::ops::{Add, Sub};
use std::marker::PhantomData;


#[derive(Clone, Debug)]
pub struct MultiBTreeSet<T: Ord> {
    values: BTreeMap<T, usize>,
    total_size: usize,
}

impl<T: Ord> MultiBTreeSet<T> {
    /// Makes a new `MultiBTreeSet`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #![allow(unused_mut)]
    /// use std::collections::BTreeSet;
    ///
    /// let mut set: MultiBTreeSet<i32> = MultuBTreeSet::new();
    /// ```
    pub fn new() -> MultiBTreeSet<T> {
        MultiBTreeSet { 
            values: BTreeMap::new(),
            total_size: 0
        }
    }

    pub fn clear(&mut self) {
        self.total_size = 0;
        self.values.clear()
    }

    pub fn get_count<Q: ?Sized>(&self, key: &Q) -> usize
        where T: Borrow<Q>,
              Q: Ord
    {
        *self.values.get(key).unwrap_or(&0)
    }

    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
        where T: Borrow<Q>,
              Q: Ord
    {
        self.get_count(value) > 0
    }

}

#[cfg(test)]
mod tests {
    use super::MultiBTreeSet;
}