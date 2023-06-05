use crate::node::Node;

pub struct Range<'a, T> {
    ptr: &'a Node<T>,
}
