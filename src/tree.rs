use crate::{
    iter::Iter,
    node::{Node, NodeKind},
    util::insert_into_vec,
};
use std::{
    borrow::Borrow,
    fmt::{Debug, Formatter},
    rc::Rc,
};

/// A set backed by B+Tree.
#[derive(Clone)]
pub struct BPlusTreeSet<T> {
    root: Node<T>,
    order: usize,
    len: usize,
}

impl<T> BPlusTreeSet<T> {
    /// Create a B+Tree set with order set to `order`.
    ///
    /// # Panic
    /// Will panci if `order` is smaller than 2.
    pub fn new(order: usize) -> Self {
        assert!(order >= 2);

        let kind = NodeKind::ROOT | NodeKind::LEAF;
        Self {
            root: Node::new(kind),
            order,
            len: 0,
        }
    }

    /// Return how many elements are stored in this set.
    #[inline]
    pub fn len(&self) -> usize {
        self.len
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
        T: Borrow<Q> + Debug,
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

    /// Insert key and pointer `kp` to the parent node of `split`, i.e.,
    /// `parents.pop().unwrap()`.
    ///
    /// We have a vector of parent nodes as this operation can be recursive.
    ///
    /// # Recursion exits:
    /// 1. `parents.is_empty()`, which means that the root node has just been split.
    /// 2. Split is no more triggered.
    fn insert_in_parent(&mut self, split: Node<T>, mut parents: Vec<Node<T>>, kp: (Rc<T>, Node<T>))
    where
        T: Ord + Debug,
    {
        if parents.is_empty() {
            // We are gonna do insertion on the parent node of `split`, but
            // unfortunately it does not have a parent node, no worries, we can
            // create one for it.
            let new_root = Node::new(NodeKind::ROOT);
            let mut new_root_write_guard = new_root.write();
            new_root_write_guard.keys.push(kp.0);
            new_root_write_guard.ptrs.extend([split, kp.1]);
            drop(new_root_write_guard);

            self.root = new_root;
        } else {
            let parent_of_split = parents.pop().expect("parents is not empty");
            let order = self.order;

            // Finally, no recursions anymore!
            if parent_of_split.len() < order {
                let mut parent_write_guard = parent_of_split.write();
                let idx = parent_write_guard
                    .ptrs
                    .binary_search(&split)
                    .expect("`split` should be there");
                parent_write_guard.ptrs.insert(idx + 1, kp.1);
                parent_write_guard.keys.insert(idx, kp.0);
            } else {
                // split `parent_of_split` (non leaf node)
                let parent_plus = Node::new(parent_of_split.kind());
                let mut parent_write_guard = parent_of_split.write();
                let mut tmp_keys = parent_write_guard.keys.drain(..).collect::<Vec<Rc<T>>>();
                let mut tmp_ptrs = parent_write_guard.ptrs.drain(..).collect::<Vec<Node<T>>>();
                let idx = tmp_keys
                    .binary_search(&kp.0)
                    .expect_err("kp.0 should not be there");
                tmp_keys.insert(idx, kp.0);
                tmp_ptrs.insert(idx + 1, kp.1);

                assert_eq!(tmp_keys.len(), order);
                assert_eq!(tmp_ptrs.len(), order + 1);

                let idx_of_k = (order as f64 / 2.0).ceil() as usize;
                parent_write_guard.keys.extend(tmp_keys.drain(0..idx_of_k));
                parent_write_guard.ptrs.extend(tmp_ptrs.drain(0..=idx_of_k));

                let k = tmp_keys.remove(0);

                let mut parent_plus_write_guard = parent_plus.write();
                parent_plus_write_guard.keys = tmp_keys;
                parent_plus_write_guard.ptrs = tmp_ptrs;

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
        T: Ord + Debug,
    {
        let order = self.order;
        let (leaf_node, parent_nodes) = self.traverse_to_leaf_node_with_parents(value.borrow());
        if leaf_node.contains(value.borrow()) {
            return false;
        }

        // `leaf_node.len()` will be either smaller than or equal to `order`.
        if leaf_node.len() < order {
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
            let leaf_node_plus = Node::new(leaf_node.kind());

            let mut leaf_node_write_guard = leaf_node.write();
            let mut leaf_node_plus_write_guard = leaf_node_plus.write();

            let mut tmp = leaf_node_write_guard.keys.drain(..).collect::<Vec<Rc<T>>>();
            insert_into_vec(&mut tmp, value);

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

            // Duplication occurs here
            let k = Rc::clone(&leaf_node_plus_write_guard.keys[0]);
            drop(leaf_node_write_guard);
            drop(leaf_node_plus_write_guard);

            self.insert_in_parent(leaf_node, parent_nodes, (k, leaf_node_plus));
        }

        self.len += 1;
        true
    }

    /// Removes a `value` from the set. Returns whether the value was present
    /// in the set.
    pub fn remove<Q>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        self.take(value).is_some()
    }

    /// Removes and returns the value in the set, if any, that is equal to the
    /// given one.
    pub fn take<Q>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        unimplemented!()
    }

    /// Return `true` is `value` is present in this set.
    #[inline]
    pub fn contains<Q>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        let leaf = self.traverse_to_leaf_node(value);
        leaf.contains(value)
    }

    /// An iterator visiting all elements in the set. The iterator element
    /// type is `Rc<T>`.
    pub fn iter(&self) -> Iter<'_, T>
    where
        T: Debug,
    {
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

impl<T: Debug> Debug for BPlusTreeSet<T> {
    // Debug print.
    // Print all the leaf nodes' keys.
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
