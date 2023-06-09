## BPlusTreeSet

A set implementation backed by B+Tree.

> This impl follows the pseudocode given in
> [Database System Concepts 7th Edition](https://www.db-book.com/).

## API

```Rust
pub fn new(order: usize) -> Self
pub fn len(&self) -> usize
pub fn is_empty(&self) -> bool
pub fn height(&self) -> usize
pub fn insert(&mut self, value: T) -> bool
pub fn remove<Q>(&mut self, value: &Q) -> bool
pub fn get<Q>(&self, value: &Q) -> Option<Rc<T>>
pub fn contains<Q>(&self, value: &Q) -> bool
pub fn iter(&self) -> Iter<'_, T>
```

## Basic Usage

```rust
use b_plus_tree_set::{BPlusTreeSet, Iter};
use std::rc::Rc;

let mut set = BPlusTreeSet::new(4);

for i in 0..3 {
    assert!(!set.contains(&i));
    assert!(set.insert(i));
}

let iter = set.iter();
assert!(iter.eq((0..3).map(|n| Rc::new(n))));

assert_eq!(set.len(), 3);
```
