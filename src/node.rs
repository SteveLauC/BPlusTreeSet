use bitflags::{bitflags, Flags};
use std::{
    borrow::Borrow,
    cell::{Ref, RefCell, RefMut},
    fmt::{Debug, Formatter},
    ops::Deref,
    rc::Rc,
};

bitflags! {
    #[derive(Debug, PartialEq, Copy, Clone, Ord, PartialOrd, Eq)]
    pub(crate) struct NodeKind: u32 {
        const ROOT = 1;
        const INTERNAL = 2;
        const LEAF = 4;
    }
}

#[derive(Debug, Ord, Eq, PartialOrd, PartialEq)]
pub(crate) struct InnerNode<T> {
    pub(crate) kind: NodeKind,
    pub(crate) keys: Vec<Rc<T>>,
    pub(crate) ptrs: Vec<Node<T>>,
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
    pub(crate) fn new(kind: NodeKind) -> Self {
        let inner = InnerNode {
            kind,
            keys: Vec::new(),
            ptrs: Vec::new(),
        };

        Self {
            inner: Rc::new(RefCell::new(inner)),
        }
    }

    /// Return the amount of **children** that this node contains.
    ///
    /// Since we are implementing a set, the pointers (other than the last one)
    /// in a leaf node does not store values, and thus should all be `NULL`.
    /// Our `ptrs` field is of type `Vec<Node<T>>`, which means we cannot
    /// represent `NULL` in our code, so leaf nodes in our implementation will
    /// ONLY have one pointer (pointing to the next leaf node).
    ///
    /// In such a case, implementing `len()` with `read_guard.ptrs.len()` would
    /// be incorrect, thus we use `read_guard.keys.len() + 1`.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.read().keys.len() + 1
    }

    /// Return `true` if this node is a leaf node.
    #[inline]
    pub(crate) fn is_leaf(&self) -> bool {
        self.read().kind.contains(NodeKind::LEAF)
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

        let len = self.len();
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
            len - 1
        }
    }

    /// Return true if this Node contains `value`.
    pub(crate) fn contains<Q>(&self, value: &Q) -> bool
    where
        Q: Ord,
        T: Borrow<Q>,
    {
        let read_guard = (&self.inner as &RefCell<InnerNode<T>>).borrow();
        read_guard
            .keys
            .binary_search_by(|item| (item as &T).borrow().cmp(value))
            .is_ok()
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

    /// Set this node's kind to `kind`.
    #[inline]
    pub(crate) fn set_kind(&self, kind: NodeKind) {
        self.write().kind = kind;
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
