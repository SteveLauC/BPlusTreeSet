use crate::{
    iter::Iter,
    node::{Node, NodeKind},
    util::insert_into_vec,
};
use std::{
    borrow::Borrow,
    fmt::{Debug, Display, Formatter},
    ops::Deref,
    rc::Rc,
};

/// A set backed by B+Tree.
#[derive(Clone, Debug)]
pub struct BPlusTreeSet<T> {
    root: Node<T>,
    order: usize,
    len: usize,
    height: usize,
}

impl<T> BPlusTreeSet<T> {
    /// Return `true` if this node is full.
    ///
    /// A full node is a valid node, but you cannot insert into it.
    ///
    /// * Leaf node
    ///   A leaf node is full if it has `order-1` search key values.
    ///
    /// * Non-leaf node
    ///   A non-leaf node is full if it has `order` pointers.
    fn node_is_full(&self, node: &Node<T>) -> bool {
        if node.is_leaf() {
            node.read().keys.len() >= (self.order - 1)
        } else {
            node.read().ptrs.len() >= self.order
        }
    }

    /// Return `true` if `node` has too few entries.
    ///
    /// A node with too few entries is **NOT** a valid node, needs to be remedied.
    ///
    /// * Leaf node
    ///   The amount of search key values is smaller than `[(n-1)/2]`.
    ///
    /// * Non-leaf node
    ///   The amount of pointers is smaller than `[n/2]`.
    ///
    /// > `[x]` denotes that the smallest integer that is bigger than `x`.
    fn node_has_too_few_entries(&self, node: &Node<T>) -> bool {
        if node.is_root() {
            if !node.is_leaf() {
                // A root that is not leaf should have at least 2 children(pointers)
                let num_children = node.read().ptrs.len();
                if num_children < 2 {
                    // If so, it should have exactly 1 child
                    assert_eq!(num_children, 1);
                    true
                } else {
                    false
                }
            } else {
                false
            }
        } else {
            let search_key_threshold = ((self.order - 1) as f64 / 2.0).ceil() as usize;
            let ptr_threshold = ((self.order as f64) / 2.0).ceil() as usize;

            if node.is_leaf() {
                node.read().keys.len() < search_key_threshold
            } else {
                node.read().ptrs.len() < ptr_threshold
            }
        }
    }

    /// Create a B+Tree set with order set to `order`.
    ///
    /// # Panic
    /// Will panic if `order` is smaller than 3.
    pub fn new(order: usize) -> Self {
        assert!(order >= 3);

        Self {
            root: Node::new(NodeKind::Leaf, true),
            order,
            len: 0,
            height: 1,
        }
    }

    /// Return how many elements are stored in this set.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Return how many levels this B+Tree has.
    #[inline]
    pub fn height(&self) -> usize {
        self.height
    }

    /// Returns true if the set contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> BPlusTreeSet<T>
where
    T: PartialOrd,
{
    /// Assume `value` exists in this B+TREE, traverse down to the leaf node
    /// that contains `value`.
    ///
    /// Use this over `traverse_to_leaf_node_with_parents()` when you do not need
    /// the collected parent nodes along the path.
    fn traverse_to_leaf_node<Q>(&self, value: &Q) -> Node<T>
    where
        Q: PartialOrd,
        T: Borrow<Q>,
    {
        let mut ptr = Node::clone(&self.root);

        while !ptr.is_leaf() {
            let idx = ptr.search_non_leaf_node(value);
            let ptr_read_guard = ptr.read();
            let node = Node::clone(&ptr_read_guard.ptrs[idx]);
            drop(ptr_read_guard);

            ptr = node;
        }

        assert!(ptr.is_leaf());

        ptr
    }

    /// Assume `value` exists in this B+TREE, traverse down to the leaf node
    /// that contains `value`.
    ///
    /// Return that leaf node and all the parent nodes.
    fn traverse_to_leaf_node_with_parents<Q>(&self, value: &Q) -> (Node<T>, Vec<Node<T>>)
    where
        Q: PartialOrd,
        T: Borrow<Q>,
    {
        // Collect parent nodes while traversing down the tree.
        let mut parent_nodes = Vec::new();
        let mut ptr = Node::clone(&self.root);

        while !ptr.is_leaf() {
            parent_nodes.push(Node::clone(&ptr));

            let idx = ptr.search_non_leaf_node(value);
            let ptr_read_guard = ptr.read();
            let node = Node::clone(&ptr_read_guard.ptrs[idx]);
            drop(ptr_read_guard);

            ptr = node;
        }

        assert!(ptr.is_leaf());

        (ptr, parent_nodes)
    }

    /// Choose a sibling that most likely makes coalescence happen.
    ///
    /// If `right` is chosen, a `true` will be returned.
    fn choose_sibling<'a>(
        left: Option<&'a Node<T>>,
        right: Option<&'a Node<T>>,
    ) -> (&'a Node<T>, bool) {
        match (left, right) {
            (Some(left), Some(right)) => {
                assert_eq!(left.kind(), right.kind());

                if left.is_leaf() {
                    if left.read().keys.len() < right.read().keys.len() {
                        (left, false)
                    } else {
                        (right, true)
                    }
                } else if left.read().ptrs.len() < right.read().ptrs.len() {
                    (left, false)
                } else {
                    (right, true)
                }
            }
            (Some(left), None) => (left, false),
            (None, Some(right)) => (right, true),
            // `parent` should be an internal node, and every internal node should
            // have at least 2 children, i.e., every node should have a sibling
            (None, None) => unreachable!("At least one of them is Some"),
        }
    }

    /// Assume `parent` is the parent node of `node`
    ///
    /// return
    /// 1. `node_plug`: `node`'s best sibling node
    ///    > Maximize the possibility of coalescence.
    ///
    /// 2. `k_plus`: the value between `node` and its sibling
    ///     > This is exactly `k` when splitting `node`
    ///
    /// 3. Index of `k_plus`
    /// 4. a bool value indicating whether `node` is a predecessor of `node_plus`
    ///
    /// # Note
    /// `node_plus` and `k_plus` are cloned from `parent`.
    fn find_sibling_and_k_plus(parent: &Node<T>, node: &Node<T>) -> (Node<T>, Rc<T>, usize, bool)
    where
        T: Ord,
    {
        let node_idx = parent
            .contains_pointer(node)
            .expect("Should be Some as `parent` should contain `node`");
        let parent_read = parent.read();

        let (left_sibling, right_sibling) = (
            node_idx
                .checked_sub(1)
                .and_then(|idx| parent_read.ptrs.get(idx)),
            node_idx
                .checked_add(1)
                .and_then(|idx| parent_read.ptrs.get(idx)),
        );
        let (sibling, node_is_predecessor) =
            BPlusTreeSet::choose_sibling(left_sibling, right_sibling);

        let k_plus_idx = if node_is_predecessor {
            node_idx
        } else {
            node_idx - 1
        };

        let k_plus = Rc::clone(&parent_read.keys[k_plus_idx]);

        (
            Node::clone(sibling),
            k_plus,
            k_plus_idx,
            node_is_predecessor,
        )
    }

    /// Return `true` if `node` and `node_plus` can fit into a single node.
    fn can_fit_in_a_single_node(&self, node: &Node<T>, node_plus: &Node<T>) -> bool {
        assert_eq!(node.kind(), node_plus.kind());
        let node_read = node.read();
        let node_plus_read = node_plus.read();

        if node.is_leaf() {
            node_read.keys.len() + node_plus_read.keys.len() < self.order
        } else {
            node_read.ptrs.len() + node_plus_read.ptrs.len() <= self.order
        }
    }

    /// Delete `value` and its `pointer` (if exists) from `node`.
    ///
    /// > Technically not "its pointer", say the index of `value` in `node`
    /// > is `i`, then the index of `pointer` would be `i+1`.
    ///
    /// This function will be used recursively when doing coalescence, use it
    /// at the leaf node first, i.e.,
    ///
    /// ```ignore
    /// let (leaf, parents) = self.traverse_to_leaf_node_with_parents(value);
    /// self.delete_entry(leaf, value, None, parents);
    /// ```
    ///
    /// `pointer` is `Option<>`al since we are implementing a set, we don't have
    /// pointers in leaf node. In recursive calls, i.e., when dealing with internal
    /// nodes using coalescence, we remove the node `node`(always the right node),
    /// and we need to clear `k_plus`(key) and `node`(pointer) from the parent
    /// node, then this argument should be `Some()`.
    fn delete_entry<Q>(
        &mut self,
        mut node: Node<T>,
        value: Rc<T>,
        pointer: Option<Node<T>>,
        mut parents: Vec<Node<T>>,
    ) where
        T: Borrow<Q> + Ord,
        Q: Ord,
    {
        // delete `(Key, pointer)` from `Node`
        let key_idx = node
            .contains(value.deref().borrow())
            .expect("This node should contain `value`");
        let ptr_idx_opt = pointer.and_then(|ptr| node.contains_pointer(&ptr));
        node.write().keys.remove(key_idx);
        if let Some(ptr_idx) = ptr_idx_opt {
            node.write().ptrs.remove(ptr_idx);
        }

        if self.node_has_too_few_entries(&node) {
            if node.is_root() {
                let new_root = node
                    .write()
                    .ptrs
                    .pop()
                    .expect("Should be Some as it has one child");
                assert!(!new_root.is_root());
                new_root.set_root(true);
                self.root = new_root;
                self.height -= 1;
                return;
            }

            let parent = parents
                .pop()
                .expect("Should be Some as `Node` has a parent node");
            let (mut node_plus, k_plus, k_plus_idx, is_predecessor) =
                BPlusTreeSet::find_sibling_and_k_plus(&parent, &node);

            // No matter it is coalescence or redistribution, for non-leaf node,
            // you need to take care of the `k_plus` key.

            if self.can_fit_in_a_single_node(&node, &node_plus) {
                // coalesce `node` and `node_plus`

                // If `node` is on the left, swap it with `node_plus` so that
                // we can always append the entries in `node` to `node_plus`
                if is_predecessor {
                    std::mem::swap(&mut node, &mut node_plus);
                }

                if !node.is_leaf() {
                    // After the deletion, the node will have `n` keys and **`n+2`**
                    // pointers, `k_plus` is the key that fulfill the gap.
                    //
                    // And, don't worry about that with the extra `k_plus` key,
                    // these keys won't fit into a single node, internal nodes
                    // cares about **pointers**.
                    node_plus.write().keys.push(Rc::clone(&k_plus));
                    // This is ONLY needed for an internal node, because for leaf
                    // node, `k_plus` is the first entry in `node`
                    /*
                        # order = 4
                        # Try delete `4` from the following tree
                        # `k_plus` is 3, node([3, 4])[0] is 3
                        # And you should recall that the `k_plus` 3 (in the root)
                        # was created when you splitting leaf node `[1, 2, 3, 4]`.
                            [3]
                           /    \
                        [1, 2] - [3, 4]
                    */

                    node_plus.write().keys.append(&mut node.write().keys);
                    node_plus.write().ptrs.append(&mut node.write().ptrs);
                } else {
                    let next_leaf = node.write().ptrs.pop();
                    assert_eq!(node.write().ptrs.len(), 0);
                    node_plus.write().keys.append(&mut node.write().keys);

                    node_plus
                        .write()
                        .ptrs
                        .pop()
                        .expect("node_plus should have a next leaf, which is node");
                    assert_eq!(node_plus.write().ptrs.len(), 0);
                    if let Some(next_leaf) = next_leaf {
                        node_plus.write().ptrs.push(next_leaf);
                    }
                }

                // After the coalescence, `node` is dead now, we need to clear
                // it from its parents.
                self.delete_entry(parent, k_plus, Some(node), parents);
            } else {
                // redistribution
                if !is_predecessor {
                    let mut node_plus_write = node_plus.write();
                    let (mut node_plus_last_key, node_plus_last_ptr) = (
                        node_plus_write
                            .keys
                            .pop()
                            .expect("Should be Some as coalescence is not possible"),
                        node_plus_write
                            .ptrs
                            .pop()
                            .expect("Should be Some as coalescence is not possible"),
                    );
                    drop(node_plus_write);

                    if !node.is_leaf() {
                        node.write().keys.insert(0, k_plus);
                        node.write().ptrs.insert(0, node_plus_last_ptr);

                        // replace `k_plus` in the `parent` with the last key in `node_plus`
                        std::mem::swap(
                            &mut parent.write().keys[k_plus_idx],
                            &mut node_plus_last_key,
                        );
                    } else {
                        node.write().keys.insert(0, Rc::clone(&node_plus_last_key));
                        node.write().ptrs.insert(0, node_plus_last_ptr);

                        // replace `k_plus` in the `parent` with the last key in `node_plus`
                        std::mem::swap(
                            &mut parent.write().keys[k_plus_idx],
                            &mut node_plus_last_key,
                        );
                    }
                } else {
                    let mut node_plus_write = node_plus.write();
                    let (mut node_plus_first_key, node_plus_first_ptr) = (
                        node_plus_write.keys.remove(0),
                        node_plus_write.ptrs.remove(0),
                    );
                    drop(node_plus_write);

                    if !node.is_leaf() {
                        node.write().keys.push(k_plus);
                        node.write().ptrs.push(node_plus_first_ptr);

                        // replace `k_plus` in the `parent` with the first key in `node_plus`
                        std::mem::swap(
                            &mut parent.write().keys[k_plus_idx],
                            &mut node_plus_first_key,
                        );
                    } else {
                        node.write().keys.push(Rc::clone(&node_plus_first_key));
                        node.write().ptrs.push(node_plus_first_ptr);

                        // replace `k_plus` in the `parent` with the first key in `node_plus`
                        std::mem::swap(
                            &mut parent.write().keys[k_plus_idx],
                            &mut node_plus_first_key,
                        );
                    }
                }
            }
        }
    }

    /// Insert key and pointer `kp` to the parent node of `split`, i.e.,
    /// `parents.pop().unwrap()`, `kp.0` is the first key in the newly-split
    /// node, `kp.1` is a pointer to that node.
    ///
    /// We have a vector of parent nodes as this operation can be recursive.
    ///
    /// # Recursion exits:
    /// 1. The root node has just been split (depth + 1)
    /// 2. Split is no more triggered.
    fn insert_in_parent(&mut self, split: Node<T>, mut parents: Vec<Node<T>>, kp: (Rc<T>, Node<T>))
    where
        T: Ord,
    {
        // This judgement, can be done by:
        // 1. split.is_root()
        // 2. parents.is_empty()
        if split.is_root() {
            // We are gonna do insertion on the parent node of `split`, but
            // unfortunately it does not have a parent node, no worries, we can
            // create one for it.

            // `split` is no longer a Root
            split.set_root(false);
            let new_root = Node::new(NodeKind::Internal, true);
            let mut new_root_write_guard = new_root.write();
            new_root_write_guard.keys.push(kp.0);
            new_root_write_guard.ptrs.extend([split, kp.1]);
            drop(new_root_write_guard);

            self.root = new_root;
            self.height += 1;
        } else {
            let parent_of_split = parents.pop().expect("parents is not empty");
            let order = self.order;

            // Finally, no recursions anymore!
            if !self.node_is_full(&parent_of_split) {
                let idx = parent_of_split
                    .contains_pointer(&split)
                    .expect("`split` should be there");
                let mut parent_write_guard = parent_of_split.write();
                parent_write_guard.ptrs.insert(idx + 1, kp.1);
                parent_write_guard.keys.insert(idx, kp.0);
            } else {
                // split `parent_of_split` (non-leaf node)
                let parent_plus = Node::new(parent_of_split.kind(), false);
                let mut parent_write_guard = parent_of_split.write();
                let mut tmp_keys = parent_write_guard.keys.drain(..).collect::<Vec<Rc<T>>>();
                let mut tmp_ptrs = parent_write_guard.ptrs.drain(..).collect::<Vec<Node<T>>>();
                let idx = tmp_keys
                    .binary_search(&kp.0)
                    .expect_err("kp.0 should not be there");
                tmp_keys.insert(idx, kp.0);
                tmp_ptrs.insert(idx + 1, kp.1);

                /*
                Let's assume the order is 3, then node tmp would be something like:

                    Key Key Key
                    Ptr Ptr Ptr Ptr

                `parent` would get one key and two pointers, the middle key (`k`)
                would be moved to the parent node of `parent`, and the last key
                and two pointers would be placed in the newly-created node
                `parent_plus`.

                    Key(parent) Key(   k  ) Key(parent_plus)
                    Ptr(parent) Ptr(parent) Ptr(parent_plus) Ptr(parent_plus)
                 */
                assert_eq!(tmp_keys.len(), order);
                assert_eq!(tmp_ptrs.len(), order + 1);

                let idx_of_k = ((order as f64 + 1.0) / 2.0).ceil() as usize - 1;
                parent_write_guard.keys.extend(tmp_keys.drain(0..idx_of_k));
                parent_write_guard.ptrs.extend(tmp_ptrs.drain(0..=idx_of_k));

                let k = tmp_keys.remove(0);

                let mut parent_plus_write_guard = parent_plus.write();
                parent_plus_write_guard.keys = tmp_keys;
                parent_plus_write_guard.ptrs = tmp_ptrs;

                assert!(!parent_write_guard.keys.is_empty());
                assert!(!parent_plus_write_guard.keys.is_empty());
                // such a constraint should be satisfied as this is an internal node.
                assert_eq!(
                    parent_plus_write_guard.keys.len() + 1,
                    parent_plus_write_guard.ptrs.len()
                );

                drop(parent_write_guard);
                drop(parent_plus_write_guard);

                self.insert_in_parent(parent_of_split, parents, (k, parent_plus));
            }
        }
    }

    /// Insert `value` into the set.
    ///
    /// Return `true` if insertion is successful.
    pub fn insert(&mut self, value: T) -> bool
    where
        T: Ord,
    {
        let order = self.order;
        let (leaf_node, parent_nodes) = self.traverse_to_leaf_node_with_parents(value.borrow());
        if leaf_node.contains(value.borrow()).is_some() {
            return false;
        }

        if !self.node_is_full(&leaf_node) {
            // have enough room, just insert
            leaf_node.insert_in_leaf(value);
        } else {
            // split leaf node
            //
            // 1. Create a new Node
            // 2. Move the entries in this `leaf_node` to `tmp`
            // 3. Insert `value` into `tmp`
            // 4. `leaf_node_plus.ptrs.last()` = `leaf_node.ptrs.last()`;
            //    `leaf_node.ptrs.last()` = `leaf_node_plus`
            //
            //     Since we are implementing a BPlusTreeSet, leaf node in such
            //     trees ONLY have one pointer, i.e., the pointer to the next
            //     leaf node.
            // 5. Move `tmp[0..(order/2)]` to `leaf_node.keys`
            // 6. Move the remaining elements in `tmp` to `leaf_node_plus`.
            // 7. Let `K'` be the smallest entry in `leaf_node_plus`, insert it
            //    and a pointer to `leaf_node_plus` to the parent node of `leaf_node`.
            let leaf_node_plus = Node::new(leaf_node.kind(), false);

            let mut leaf_node_write_guard = leaf_node.write();
            let mut leaf_node_plus_write_guard = leaf_node_plus.write();

            let mut tmp = leaf_node_write_guard.keys.drain(..).collect::<Vec<Rc<T>>>();
            insert_into_vec(&mut tmp, value);
            // not `tmp` has `order` keys
            assert_eq!(tmp.len(), self.order);

            if !leaf_node_write_guard.ptrs.is_empty() {
                assert_eq!(leaf_node_write_guard.ptrs.len(), 1);
                leaf_node_plus_write_guard.ptrs.push(
                    leaf_node_write_guard
                        .ptrs
                        .pop()
                        .expect("Should have exactly 1 ptr"),
                );
            }
            leaf_node_write_guard
                .ptrs
                .push(Node::clone(&leaf_node_plus));

            assert_eq!(leaf_node_write_guard.keys.len(), 0);
            let idx = (order as f64 / 2.0).ceil() as usize;
            leaf_node_write_guard.keys.extend(tmp.drain(0..idx));
            leaf_node_plus_write_guard.keys = tmp;

            // key duplication occurs here
            let k = Rc::clone(&leaf_node_plus_write_guard.keys[0]);

            assert!(!leaf_node_write_guard.keys.is_empty());
            assert!(!leaf_node_plus_write_guard.keys.is_empty());

            drop(leaf_node_write_guard);
            drop(leaf_node_plus_write_guard);

            self.insert_in_parent(leaf_node, parent_nodes, (k, leaf_node_plus));
        }

        self.len += 1;
        true
    }

    /// Removes a `value` from the set. Returns whether the value was present
    /// in the set.
    ///
    /// We cannot return the deleted `T` as there is possibly still `Rc<T>` in
    /// the tree.
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q> + Ord,
        Q: Ord,
    {
        let (leaf, parents) = self.traverse_to_leaf_node_with_parents(value);

        if let Some(idx) = leaf.contains(value) {
            let key = Rc::clone(&leaf.read().keys[idx]);
            self.delete_entry(leaf, key, None, parents);
            self.len -= 1;
            true
        } else {
            false
        }
    }

    /// Return `true` is `value` is present in this set.
    #[inline]
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        let leaf = self.traverse_to_leaf_node(value);
        leaf.contains(value).is_some()
    }

    /// Returns a `Rc` to the value in the set, if any.
    pub fn get<Q>(&self, value: &Q) -> Option<Rc<T>>
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        let leaf = self.traverse_to_leaf_node(value);
        let leaf_guard = leaf.read();
        let idx = leaf_guard
            .keys
            .binary_search_by(|item| (item as &T).borrow().cmp(value))
            .ok()?;

        Some(Rc::clone(&leaf_guard.keys[idx]))
    }

    /// An iterator visiting all elements in the set. The iterator element
    /// type is `Rc<T>`.
    pub fn iter(&self) -> Iter<'_, T> {
        let mut ptr = Node::clone(&self.root);
        while !ptr.is_leaf() {
            let ptr_guard = ptr.read();
            let next = Node::clone(
                ptr_guard
                    .ptrs
                    .first()
                    .expect("Should have at least 2 children"),
            );
            drop(ptr_guard);

            ptr = next;
        }
        assert!(ptr.is_leaf());
        let len = ptr.read().keys.len();

        Iter::new(ptr, 0, len)
    }
}

impl<T: Debug> Display for BPlusTreeSet<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut ptr = Node::clone(&self.root);

        while !ptr.is_leaf() {
            let read_guard = ptr.read();
            let node = Node::clone(read_guard.ptrs.first().unwrap());
            drop(read_guard);

            ptr = node;
        }

        loop {
            let ptr_read = ptr.read();
            write!(f, "{:?}", ptr_read.keys)?;

            if !ptr_read.ptrs.is_empty() {
                let node = Node::clone(ptr_read.ptrs.first().unwrap());
                drop(ptr_read);

                ptr = node;
                continue;
            } else {
                break;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn node_is_full() {
        let tree = BPlusTreeSet::new(4);
        let leaf = Node::new(NodeKind::Leaf, false);
        leaf.write().keys.extend((1..3).map(|i| Rc::new(i)));
        assert!(!tree.node_is_full(&leaf));
        leaf.write().keys.push(Rc::new(4));
        assert!(tree.node_is_full(&leaf));

        let internal = Node::new(NodeKind::Internal, false);
        internal
            .write()
            .ptrs
            .extend((1..4).map(|_| Node::new(NodeKind::Leaf, false)));
        assert!(!tree.node_is_full(&internal));
        internal.write().ptrs.push(Node::new(NodeKind::Leaf, false));
        assert!(tree.node_is_full(&internal));
    }

    #[test]
    fn non_root_node_has_too_few_entries() {
        let tree = BPlusTreeSet::new(4);
        let leaf = Node::new(NodeKind::Leaf, false);
        leaf.write().keys.push(Rc::new(1));
        assert!(tree.node_has_too_few_entries(&leaf));
        leaf.write().keys.push(Rc::new(2));
        assert!(!tree.node_has_too_few_entries(&leaf));

        let internal = Node::new(NodeKind::Internal, false);
        internal
            .write()
            .ptrs
            .push(Node::new(NodeKind::Internal, false));
        assert!(tree.node_has_too_few_entries(&internal));
        internal.write().ptrs.push(Node::new(NodeKind::Leaf, false));
        assert!(!tree.node_has_too_few_entries(&internal));
    }
}
