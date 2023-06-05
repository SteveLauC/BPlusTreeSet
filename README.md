## BPlusTreeSet

A set implementation backed by B+Tree.

## API

```Rust
pub fn new(order: usize) -> Self
pub fn len(&self) -> usize
pub fn insert(&mut self, value: T) -> bool
pub fn remove<Q>(&mut self, value: &Q) -> bool
pub fn take<Q>(&mut self, value: &Q) -> Option<T>
pub fn contains<Q>(&self, value: &Q) -> bool
```

## Basic Usage

```rust
use b_plus_tree_set::BPlusTreeSet;

let mut set = BPlusTreeSet::new(4);

for i in 0..10 {
    assert!(!set.contains(&i));
    assert!(set.insert(i));
}

assert_eq!(set.len(), 10);
```
