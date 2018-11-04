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
    pub fn new() -> MultiBTreeSet<T> {
        MultiBTreeSet { 
            values: BTreeMap::new(),
            total_size: 0
        }
    }
}


#[cfg(test)]
mod tests {
    use super::MultiBTreeSet;
}