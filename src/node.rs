use std::{
    borrow::Borrow,
    cell::{Ref, RefCell, RefMut},
    cmp::Ordering,
    fmt::{Debug, Formatter},
    ops::Deref,
    rc::Rc,
};

/// Node Kind
///
/// A Root node can be either a leaf node or a internal node, thus, we use a
/// dedicated field to store it.
#[derive(Debug, PartialEq, Copy, Clone, Ord, PartialOrd, Eq)]
pub(crate) enum NodeKind {
    Internal,
    Leaf,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct InnerNode<T> {
    /// A Root node can be either a leaf node or a internal node, thus, we use a
    /// dedicated field to store it.
    is_root: bool,
    kind: NodeKind,

    pub(crate) keys: Vec<Rc<T>>,
    pub(crate) ptrs: Vec<Node<T>>,
}

impl<T: PartialOrd> PartialOrd for InnerNode<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else {
            self.keys
                .first()
                .unwrap()
                .partial_cmp(other.keys.first().unwrap())
        }
    }
}

impl<T: PartialOrd + Ord> Ord for InnerNode<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        if self == other {
            Ordering::Equal
        } else {
            self.keys.first().unwrap().cmp(other.keys.first().unwrap())
        }
    }
}

/// A `Node` in a B+TREE
///
/// `Rc` is used as a leaf node can have more than 1 owner (Maybe 2? One is its
/// parent node, the other one is the previous leaf node).
#[derive(Ord, PartialOrd, Eq, PartialEq)]
pub(crate) struct Node<T> {
    pub(crate) inner: Rc<RefCell<InnerNode<T>>>,
}

impl<T: Debug> Debug for Node<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let guard = self.read();
        write!(f, "{:?}", *guard.deref())
    }
}

impl<T> Node<T> {
    /// Create an empty `kind` Node.
    pub(crate) fn new(kind: NodeKind, is_root: bool) -> Self {
        let inner = InnerNode {
            is_root,
            kind,
            keys: Vec::new(),
            ptrs: Vec::new(),
        };

        Self {
            inner: Rc::new(RefCell::new(inner)),
        }
    }

    /// Return `true` if this node is a leaf node.
    ///
    /// Since we ONLY have two kinds of node:
    /// 1. Leaf node
    /// 2. Internal node
    ///
    /// Use `!node.is_leaf()` if you wanna determine if a node is an internal node.
    #[inline]
    pub(crate) fn is_leaf(&self) -> bool {
        self.read().kind == NodeKind::Leaf
    }

    /// Return `true` is this Node is root.
    #[inline]
    pub(crate) fn is_root(&self) -> bool {
        self.read().is_root
    }

    /// Set `is_root` for this Node.
    #[inline]
    pub(crate) fn set_root(&self, is_root: bool) {
        self.write().is_root = is_root;
    }

    /// Helper function to help search `value` in a B+Tree.
    ///
    /// Search the smallest element that is greater than or equal to `value`,
    /// return which sub-tree we should navigate to.
    pub(crate) fn search_non_leaf_node<Q>(&self, value: &Q) -> usize
    where
        Q: PartialOrd,
        T: Borrow<Q>,
    {
        assert!(!self.is_leaf());

        let read_guard = self.read();

        let idx_opt = read_guard
            .keys
            .iter()
            .position(|item| item.deref().borrow() >= value);

        if let Some(idx) = idx_opt {
            if read_guard.keys[idx].deref().borrow() > value {
                idx
            } else {
                idx + 1
            }
        } else {
            read_guard.ptrs.len() - 1
        }
    }

    /// Return `Some(idx)` if this Node contains `value`.
    pub(crate) fn contains<Q>(&self, value: &Q) -> Option<usize>
    where
        Q: Ord,
        T: Borrow<Q>,
    {
        let read_guard = self.read();
        let idx = read_guard
            .keys
            .binary_search_by(|item| (item as &T).borrow().cmp(value))
            .ok()?;

        Some(idx)
    }

    /// Return `Some(idx)` if this Node contains `pointer`
    pub(crate) fn contains_pointer(&self, node: &Node<T>) -> Option<usize>
    where
        T: Ord,
    {
        let read_guard = self.read();
        let idx = read_guard.ptrs.binary_search(node).ok()?;
        Some(idx)
    }

    /// Insert `value` into this leaf node.
    ///
    /// Assume that `value` does not exist in this node and split won't happen.
    pub(crate) fn insert_in_leaf(&self, value: T)
    where
        T: Ord,
    {
        assert!(self.is_leaf());

        let value = Rc::new(value);
        let mut write_guard = self.write();
        let idx = write_guard
            .keys
            .binary_search_by(|item| item.deref().cmp(&value))
            .expect_err("This Node should not contain `value`");

        write_guard.keys.insert(idx, value);
    }

    /// Return this node's kind.
    #[inline]
    pub(crate) fn kind(&self) -> NodeKind {
        self.read().kind
    }

    /// Acquire a Read Guard to `self.`
    pub(crate) fn read(&self) -> Ref<InnerNode<T>> {
        self.inner.deref().borrow()
    }

    /// Acquire a Write Guard to `self.`
    pub(crate) fn write(&self) -> RefMut<InnerNode<T>> {
        self.inner.deref().borrow_mut()
    }
}

impl<T> Clone for Node<T> {
    fn clone(&self) -> Self {
        Self {
            inner: Rc::clone(&self.inner),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn nodes_equal() {
        let node1 = Node::new(NodeKind::Internal, false);
        node1.write().keys.push(Rc::new(1));

        let node2 = Node::new(NodeKind::Internal, false);
        node2.write().keys.push(Rc::new(1));

        assert_eq!(node1, node2);
    }

    #[test]
    fn nodes_not_equal() {
        let node1 = Node::new(NodeKind::Internal, false);
        node1.write().keys.push(Rc::new(1));

        let node2 = Node::new(NodeKind::Internal, false);

        assert_ne!(node1, node2);
    }

    #[test]
    fn nodes_gt() {
        let node1 = Node::new(NodeKind::Internal, false);
        node1.write().keys.push(Rc::new(1));

        let node2 = Node::new(NodeKind::Internal, false);
        node2.write().keys.push(Rc::new(0));

        assert!(node1 > node2);
    }

    #[test]
    fn contains() {
        let node = Node::new(NodeKind::Internal, false);
        node.write().keys.extend((1..10).map(|i| Rc::new(i)));

        assert_eq!(node.contains(&0), None);
        assert_eq!(node.contains(&1), Some(0));
        assert_eq!(node.contains(&10), None);
    }

    #[test]
    fn contains_pointer() {
        let test_node: Node<i32> = Node::new(NodeKind::Internal, false);

        for i in 0..10 {
            let node = Node::new(NodeKind::Internal, false);
            node.write().keys.push(Rc::new(i));

            test_node.write().ptrs.push(node);
        }

        for i in 0..10 {
            let node = Node::new(NodeKind::Internal, false);
            node.write().keys.push(Rc::new(i));

            assert_eq!(test_node.contains_pointer(&node), Some(i as usize))
        }
    }
}
