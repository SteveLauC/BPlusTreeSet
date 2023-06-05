#![doc = include_str!("../README.md")]

mod node;
mod tree;
mod util;

pub use tree::BPlusTreeSet;

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn new() {
        let set: BPlusTreeSet<i32> = BPlusTreeSet::new(4);

        assert_eq!(set.len(), 0);
    }

    #[test]
    fn insert() {
        let mut set = BPlusTreeSet::new(4);

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
}
