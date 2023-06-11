#![doc = include_str!("../README.md")]

mod iter;
mod node;
mod tree;
mod util;

pub use iter::Iter;
pub use tree::BPlusTreeSet;

#[cfg(test)]
mod test {
    use super::*;
    use std::rc::Rc;

    #[test]
    fn new() {
        let set: BPlusTreeSet<i32> = BPlusTreeSet::new(4);

        assert_eq!(set.len(), 0);
    }

    #[test]
    fn insert() {
        let mut set = BPlusTreeSet::new(4);
        assert!(set.is_empty());

        for i in 0..10 {
            assert!(!set.contains(&i));
            assert!(set.insert(i));
        }

        for i in 0..10 {
            assert!(!set.insert(i));
            assert!(set.contains(&i));
        }

        assert_eq!(set.len(), 10);
    }

    #[test]
    fn get() {
        let mut set = BPlusTreeSet::new(4);
        assert!(set.get(&1).is_none());
        assert!(set.insert(1));

        let one = set.get(&1).unwrap();
        assert_eq!(Rc::strong_count(&one), 2);
    }

    #[test]
    fn delete_in_single_node_tree() {
        let mut set = BPlusTreeSet::new(4);
        for i in 0..3 {
            assert!(!set.contains(&i));
            assert!(set.insert(i));
        }

        println!("{:?}", set);

        for i in 0..3 {
            assert!(set.contains(&i));
            assert!(set.remove(&i));
            assert!(!set.contains(&i));
        }

        assert!(set.is_empty());
    }
}
