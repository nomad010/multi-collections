use std::collections::{BTreeMap};
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