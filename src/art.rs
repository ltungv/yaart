use std::borrow::Borrow;

use crate::{
    node::{debug_print, Node},
    BytesComparable,
};

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
            .and_then(|node| node.search(key.key().into_ref(), 0))
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
        let mut root = self.root.take()?;
        // Handles special case when the root is a leaf. Otherwise, start deleting from within the inner node.
        let Node::Leaf(leaf) = root else {
            let deleted = root.delete(key.key().into_ref(), 0).map(|leaf| leaf.value);
            self.root = Some(root);
            return deleted;
        };
        // If the key matches, return the leaf's value. Otherwise, put it back as the root.
        if !leaf.match_key(key.key().into_ref()) {
            self.root = Some(Node::Leaf(leaf));
            return None;
        }
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

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, ops::Range};

    use rand::{
        distr::{Alphanumeric, Distribution, StandardUniform},
        seq::SliceRandom,
        Rng, SeedableRng,
    };

    use crate::ART;

    fn get_samples<T>(
        seed: u64,
        prefix_count: usize,
        prefix_sizes: Range<usize>,
        suffix_count: usize,
        suffix_size: usize,
    ) -> Vec<(String, T)>
    where
        StandardUniform: Distribution<T> + Distribution<u64>,
    {
        let random_string = |seed: u64, size: usize| {
            rand::rngs::StdRng::seed_from_u64(seed)
                .sample_iter(Alphanumeric)
                .map(char::from)
                .take(size)
                .collect::<String>()
        };
        let mut rng = rand::rngs::StdRng::seed_from_u64(seed);
        let mut keys = Vec::new();
        for prefix_size in prefix_sizes {
            let mut prefixes = Vec::default();
            for _ in 0..prefix_count {
                prefixes.push(random_string(rng.random(), prefix_size));
            }
            for suffix_index in 0..suffix_count {
                let mut key = String::new();
                for prefix in prefixes.iter().take(suffix_index % prefix_count) {
                    key.push_str(prefix);
                }
                key.push_str(&random_string(rng.random(), suffix_size));
                keys.push((key, rng.random()));
            }
        }
        keys.shuffle(&mut rng);
        keys
    }

    #[test]
    fn test_insert_tree_tiny() {
        let mut radix = ART::<String, String>::default();
        radix.insert("hell".to_string(), "boy".to_string());
        radix.insert("hello".to_string(), "world".to_string());
        let v0 = radix.search("hell");
        let v1 = radix.search("hello");
        assert_eq!(v0.map(String::as_str), Some("boy"));
        assert_eq!(v1.map(String::as_str), Some("world"));
    }

    #[test]
    fn test_all_operations() {
        let samples = get_samples::<u32>(rand::random(), 32, 2..18, 256, 8);
        let mut radix = ART::<_, _, 10>::default();
        let mut btree = BTreeMap::new();

        for (k, v) in &samples {
            radix.insert(k.clone(), *v);
            btree.insert(k.clone(), *v);
        }

        assert_eq!(radix.min(), btree.first_key_value());
        assert_eq!(radix.max(), btree.last_key_value());
        for (k, v) in &btree {
            assert_eq!(radix.search(k), Some(v));
            assert_eq!(radix.delete(k), Some(*v));
            assert_eq!(radix.search(k), None);
            assert_eq!(radix.delete(k), None);
        }
    }
}
