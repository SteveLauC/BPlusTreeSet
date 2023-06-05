use crate::node::Node;
use std::{
    fmt::{Debug, Formatter},
    rc::Rc,
};

/// An iterator over the items of a `BPlusTreeSet`.
pub struct Iter<'a, T> {
    node: Node<T>,
    keys_idx: usize,
    keys_len: usize,

    marker: std::marker::PhantomData<&'a T>,
}

impl<T: Debug> Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let node_guard = self.node.read();
        f.debug_struct("Iter")
            .field("node_keys", &node_guard.keys)
            .field("keys_idx", &self.keys_idx)
            .finish()
    }
}

impl<'a, T> Iter<'a, T> {
    pub(crate) fn new(node: Node<T>, keys_idx: usize, keys_len: usize) -> Self {
        Self {
            node,
            keys_len,
            keys_idx,

            marker: std::marker::PhantomData,
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    // We cannot return a `&'a T` since it is behind the `Ref` guard.
    type Item = Rc<T>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.keys_idx == self.keys_len {
                let node_guard = self.node.read();
                let next_leaf = node_guard.ptrs.last()?;
                let next_leaf_guard = next_leaf.read();

                // Cannot write:
                //
                // ```rust
                // self.node = Node::clone(next_leaf);
                // self.keys_len = next_leaf_guard.keys.len();
                // ```
                //
                // We can not assign to `self` as it is borrowed by `node_guard`,
                // `next_leaf_guard`...
                let next = Node::clone(next_leaf);
                let new_keys_len = next_leaf_guard.keys.len();

                drop(next_leaf_guard);
                drop(node_guard);

                self.node = next;
                self.keys_len = new_keys_len;
                self.keys_idx = 0;

                continue;
            }

            let node_guard = self.node.read();
            let ret = Some(Rc::clone(&node_guard.keys[self.keys_idx]));
            self.keys_idx += 1;

            return ret;
        }
    }
}
