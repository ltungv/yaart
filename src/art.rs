//! # Adaptive Radix Tree.

mod node;

use std::borrow::Borrow;

use self::node::Node;

/// An adaptive radix tree.
#[derive(Default)]
pub struct Tree<K, V, const N: usize = 10> {
    root: Option<Node<K, V, N>>,
}

impl<K, V, const N: usize> std::fmt::Debug for Tree<K, V, N>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Some(root) = &self.root else {
            return writeln!(f, "empty");
        };
        root.debug_print(f, 0, 0)
    }
}

impl<K, V, const N: usize> Tree<K, V, N>
where
    K: BytesComparable,
{
    /// Search for the value associated with the given key.
    pub fn search<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: BytesComparable + ?Sized,
    {
        self.root
            .as_ref()
            .and_then(|node| node.search(key.bytes().as_ref(), 0))
            .map(|leaf| &leaf.value)
    }

    /// Insert the given key-value pair into the tree.
    pub fn insert(&mut self, key: K, value: V) {
        if let Some(ref mut root) = self.root {
            // Recursively insert the key-value pair into the tree.
            return root.insert(key, value, 0);
        }
        // Simply create a new leaf to replace the current root.
        self.root = Some(Node::new_leaf(key, value));
    }

    /// Delete the value associated with the given key.
    pub fn delete<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: BytesComparable + ?Sized,
    {
        // Take the root node out so we can easily work with it.
        let Some(mut root) = self.root.take() else {
            // Stop if the tree is empty.
            return None;
        };

        // Extract the leaf to check if the keys match.
        let Node::Leaf(leaf) = root else {
            // If the root is an inner node, recursively delete the key from it. Once finished,
            // put the root back into the tree.
            let prev = root.delete(key.bytes().as_ref(), 0).and_then(|node| {
                if let Node::Leaf(leaf) = node {
                    Some(leaf.value)
                } else {
                    None
                }
            });
            self.root = Some(root);
            return prev;
        };

        if !leaf.match_key(key.bytes().as_ref()) {
            // If the key doesn't match, put the root back into the tree.
            self.root = Some(Node::Leaf(leaf));
            return None;
        };

        // The keys match, so we don't put the root back into the tree and return the value.
        Some(leaf.value)
    }

    /// Find the minimum key-value pair in the tree.
    #[must_use]
    pub fn min(&self) -> Option<(&K, &V)> {
        self.root
            .as_ref()
            .and_then(|root| root.min_leaf().map(|leaf| (&leaf.key, &leaf.value)))
    }

    /// Find the maximum key-value pair in the tree.
    #[must_use]
    pub fn max(&self) -> Option<(&K, &V)> {
        self.root
            .as_ref()
            .and_then(|root| root.max_leaf().map(|leaf| (&leaf.key, &leaf.value)))
    }
}

/// A type that can be turn into bytes for comparison.
pub trait BytesComparable {
    /// The container type that holds the bytes representing our value, which can be
    /// referenced to get the slice of bytes.
    type Target<'a>: 'a + AsRef<[u8]>
    where
        Self: 'a;

    /// Turn the value into a container of bytes.
    fn bytes(&self) -> Self::Target<'_>;
}

impl BytesComparable for u8 {
    type Target<'a> = [Self; 1];

    fn bytes(&self) -> Self::Target<'static> {
        self.to_be_bytes()
    }
}

impl BytesComparable for u16 {
    type Target<'a> = [u8; 2];

    fn bytes(&self) -> Self::Target<'static> {
        self.to_be_bytes()
    }
}

impl BytesComparable for u32 {
    type Target<'a> = [u8; 4];

    fn bytes(&self) -> Self::Target<'static> {
        self.to_be_bytes()
    }
}

impl BytesComparable for u64 {
    type Target<'a> = [u8; 8];

    fn bytes(&self) -> Self::Target<'static> {
        self.to_be_bytes()
    }
}

impl BytesComparable for u128 {
    type Target<'a> = [u8; 16];

    fn bytes(&self) -> Self::Target<'static> {
        self.to_be_bytes()
    }
}

impl BytesComparable for i8 {
    type Target<'a> = [u8; 1];

    fn bytes(&self) -> Self::Target<'static> {
        (self ^ (1 << (Self::BITS - 1))).to_be_bytes()
    }
}

impl BytesComparable for i16 {
    type Target<'a> = [u8; 2];

    fn bytes(&self) -> Self::Target<'static> {
        (self ^ (1 << (Self::BITS - 1))).to_be_bytes()
    }
}

impl BytesComparable for i32 {
    type Target<'a> = [u8; 4];

    fn bytes(&self) -> Self::Target<'static> {
        (self ^ (1 << (Self::BITS - 1))).to_be_bytes()
    }
}

impl BytesComparable for i64 {
    type Target<'a> = [u8; 8];

    fn bytes(&self) -> Self::Target<'static> {
        (self ^ (1 << (Self::BITS - 1))).to_be_bytes()
    }
}

impl BytesComparable for i128 {
    type Target<'a> = [u8; 16];

    fn bytes(&self) -> Self::Target<'static> {
        (self ^ (1 << (Self::BITS - 1))).to_be_bytes()
    }
}

impl BytesComparable for String {
    type Target<'a> = &'a [u8];

    fn bytes(&self) -> Self::Target<'_> {
        self.as_bytes()
    }
}

impl BytesComparable for str {
    type Target<'a> = &'a [u8];

    fn bytes(&self) -> Self::Target<'_> {
        self.as_bytes()
    }
}

impl BytesComparable for &str {
    type Target<'a> = &'a [u8] where Self: 'a ;

    fn bytes(&self) -> Self::Target<'_> {
        self.as_bytes()
    }
}

impl BytesComparable for Vec<u8> {
    type Target<'a> = &'a [u8];

    fn bytes(&self) -> Self::Target<'_> {
        self.as_slice()
    }
}

impl BytesComparable for [u8] {
    type Target<'a> = &'a [u8];

    fn bytes(&self) -> Self::Target<'_> {
        self
    }
}

impl BytesComparable for &[u8] {
    type Target<'a> = &'a [u8] where Self: 'a;

    fn bytes(&self) -> Self::Target<'_> {
        self
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashMap, ops::Range};

    use rand::{distributions::Alphanumeric, seq::SliceRandom, Rng};

    use crate::Tree;

    fn get_key_samples(
        prefix_sizes: Range<usize>,
        suffix_count: usize,
        suffix_size: usize,
    ) -> Vec<String> {
        let mut keys = Vec::new();
        for prefix_len in prefix_sizes {
            let prefix: String = rand::thread_rng()
                .sample_iter(Alphanumeric)
                .map(char::from)
                .take(prefix_len)
                .collect();

            for _ in 0..suffix_count {
                let suffix: String = rand::thread_rng()
                    .sample_iter(Alphanumeric)
                    .map(char::from)
                    .take(suffix_size)
                    .collect();
                keys.push(prefix.clone() + &suffix);
            }
        }
        let mut rng = rand::thread_rng();
        keys.shuffle(&mut rng);
        keys
    }

    #[test]
    fn test_insert_tree_tiny() {
        let mut tree = Tree::<String, String>::default();
        tree.insert("hell".to_string(), "boy".to_string());
        tree.insert("hello".to_string(), "world".to_string());
        let v0 = tree.search("hell");
        let v1 = tree.search("hello");
        assert_eq!(v0.map(String::as_str), Some("boy"));
        assert_eq!(v1.map(String::as_str), Some("world"));
    }

    #[test]
    fn test_all_operations() {
        let keys = get_key_samples(0..256, 256, 64);
        let mut rng = rand::thread_rng();
        let mut tree = Tree::<_, _, 10>::default();
        let mut hash = HashMap::new();

        for key in keys {
            let v: u32 = rng.gen();
            tree.insert(key.clone(), v);
            hash.insert(key.clone(), v);
        }

        for (k, v) in &hash {
            assert_eq!(tree.search(k), Some(v));
            assert_eq!(tree.delete(k), Some(*v));
            assert_eq!(tree.search(k), None);
            assert_eq!(tree.delete(k), None);
        }
    }
}
