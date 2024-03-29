//! # Adaptive Radix Tree

#![warn(
    clippy::pedantic,
    clippy::cargo,
    clippy::nursery,
    rustdoc::all,
    missing_debug_implementations
)]
#![deny(clippy::all, missing_docs, rust_2018_idioms, rust_2021_compatibility)]

mod indices;
mod node;

use std::borrow::Borrow;

use self::node::{debug_print, Node};

/// An adaptive radix tree.
#[derive(Default)]
pub struct ART<K, V, const N: usize = 10> {
    root: Option<Node<K, V, N>>,
}

impl<K, V, const N: usize> std::fmt::Debug for ART<K, V, N>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(root) = &self.root {
            debug_print(f, root, 0, 0)
        } else {
            writeln!(f, "empty")
        }
    }
}

impl<K, V, const N: usize> ART<K, V, N>
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
        // Insert into the current root if the tree is not empty. Otherwise,
        // create a new leaf as the root.
        if let Some(ref mut root) = self.root {
            root.insert(key, value, 0);
        } else {
            self.root = Some(Node::new_leaf(key, value));
        }
    }

    /// Delete the value associated with the given key.
    pub fn delete<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: BytesComparable + ?Sized,
    {
        let Some(mut root) = self.root.take() else {
            return None;
        };
        // Handles special case when the root is a leaf. Otherwise, start deleting from within the inner node.
        let Node::Leaf(leaf) = root else {
            let deleted = root.delete(key.bytes().as_ref(), 0).map(|leaf| leaf.value);
            self.root = Some(root);
            return deleted;
        };
        // If the key matches, return the leaf's value. Otherwise, put it back as the root.
        if !leaf.match_key(key.bytes().as_ref()) {
            self.root = Some(Node::Leaf(leaf));
            return None;
        };
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

    use crate::ART;

    fn get_key_samples(
        prefix_sizes: Range<usize>,
        suffix_count: usize,
        suffix_size: usize,
    ) -> Vec<String> {
        let random_string = |size: usize| {
            rand::thread_rng()
                .sample_iter(Alphanumeric)
                .map(char::from)
                .take(size)
                .collect::<String>()
        };
        let mut keys = Vec::new();
        for prefix_size in prefix_sizes {
            let prefix1: String = random_string(prefix_size);
            let prefix2: String = random_string(prefix_size);
            let prefix3: String = random_string(prefix_size);
            for suffix_index in 0..suffix_count {
                let mut key = String::new();
                match suffix_index % 3 {
                    0 => key.push_str(&prefix1),
                    1 => {
                        key.push_str(&prefix1);
                        key.push_str(&prefix2);
                    }
                    _ => {
                        key.push_str(&prefix1);
                        key.push_str(&prefix2);
                        key.push_str(&prefix3);
                    }
                }
                key.push_str(&random_string(suffix_size));
                keys.push(key);
            }
        }
        let mut rng = rand::thread_rng();
        keys.shuffle(&mut rng);
        keys
    }

    #[test]
    fn test_insert_tree_tiny() {
        let mut tree = ART::<String, String>::default();
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
        let mut tree = ART::<_, _, 10>::default();
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
