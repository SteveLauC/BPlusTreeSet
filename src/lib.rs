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
        assert_eq!(set.height(), 1);
    }

    #[test]
    fn insert_order_3() {
        let mut set = BPlusTreeSet::new(3);
        assert!(set.is_empty());

        for i in 1..8 {
            assert!(!set.contains(&i));
            assert!(set.insert(i));
        }
        /*
                  [5]
              /         \
          [3] ------------[7]
         /    \         /    \
        [1, 2]-[3, 4]-[5, 6]-[7]
        */

        for i in 1..8 {
            assert!(!set.insert(i));
            assert!(set.contains(&i));
        }

        assert_eq!(set.len(), 7);
        assert_eq!(set.height(), 3);
    }

    #[test]
    fn insert() {
        let mut set = BPlusTreeSet::new(4);
        assert!(set.is_empty());

        for i in 1..11 {
            assert!(!set.contains(&i));
            assert!(set.insert(i));
        }

        for i in 1..11 {
            assert!(!set.insert(i));
            assert!(set.contains(&i));
        }

        assert_eq!(set.len(), 10);
        assert_eq!(set.height(), 3);
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

    #[test]
    fn delete_that_shrinks_the_tree() {
        let mut set = BPlusTreeSet::new(4);
        for i in 1..5 {
            set.insert(i);
        }

        /*
              [3]
             /   \
        [1, 2] ->  [3, 4]
        */
        assert_eq!(set.height(), 2);
        set.remove(&4);

        /*
        [1, 2, 3]
        */
        assert_eq!(set.height(), 1);
    }

    #[test]
    fn delete_without_redistribution() {
        let mut set = BPlusTreeSet::new(3);

        for i in 0..15 {
            assert!(set.insert(i));
        }
        assert_eq!(set.len(), 15);

        for i in 0..15 {
            assert!(set.contains(&i));
            assert!(set.remove(&i));
            assert!(!set.contains(&i));
        }

        assert_eq!(set.len(), 0);
        assert_eq!(set.height(), 1);
    }

    #[test]
    fn delete_redistribution() {
        let mut set = BPlusTreeSet::new(3);

        for i in 0..100 {
            assert!(set.insert(i));
        }
        assert_eq!(set.len(), 100);

        for i in 0..100 {
            assert!(set.contains(&i));
            assert!(set.remove(&i));
            assert!(!set.contains(&i));
        }

        assert_eq!(set.len(), 0);
        assert_eq!(set.height(), 1);
    }
}
