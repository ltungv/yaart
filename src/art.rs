//! # Adaptive Radix Tree.

use std::{borrow::Borrow, cmp::min};

use crate::indices::{Direct, Indices, Indirect, Sorted};

/// An adaptive radix tree.
#[derive(Default)]
pub struct Tree<K, V> {
    root: Option<Node<K, V, 8>>,
}

impl<K, V> std::fmt::Debug for Tree<K, V>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(root) = &self.root {
            return root.debug_print_node(f, 0, 0);
        }
        writeln!(f, "empty")
    }
}

impl<K, V> Tree<K, V>
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
            // If the root is an internal node, recursively delete the key from it. Once finished,
            // put the root back into the tree.
            let prev = root.delete(key.bytes().as_ref(), 0);
            self.root = Some(root);
            return prev.and_then(|deleted| {
                if let Node::Leaf(deleted_leaf) = deleted {
                    Some(deleted_leaf.value)
                } else {
                    None
                }
            });
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
        self.root.as_ref().and_then(|root| match root {
            Node::Leaf(leaf) => Some((&leaf.key, &leaf.value)),
            Node::Inner(inner) => inner
                .indices
                .min_leaf()
                .map(|leaf| (&leaf.key, &leaf.value)),
        })
    }

    /// Find the maximum key-value pair in the tree.
    #[must_use]
    pub fn max(&self) -> Option<(&K, &V)> {
        self.root.as_ref().and_then(|root| match root {
            Node::Leaf(leaf) => Some((&leaf.key, &leaf.value)),
            Node::Inner(inner) => inner
                .indices
                .max_leaf()
                .map(|leaf| (&leaf.key, &leaf.value)),
        })
    }
}

#[derive(Debug)]
enum Node<K, V, const P: usize> {
    Leaf(Box<Leaf<K, V>>),
    Inner(Inner<K, V, P>),
}

impl<K, V, const P: usize> Node<K, V, P> {
    fn new_leaf(key: K, value: V) -> Self {
        Self::Leaf(Box::new(Leaf { key, value }))
    }

    fn new_internal(partial: PartialKey<P>) -> Self {
        Self::Inner(Inner::new(partial))
    }
}

impl<K, V, const P: usize> Node<K, V, P>
where
    K: BytesComparable,
{
    fn search(&self, key: &[u8], depth: usize) -> Option<&Leaf<K, V>> {
        match &self {
            Self::Leaf(leaf) => {
                if leaf.match_key(key) {
                    return Some(leaf);
                }
                None
            }
            Self::Inner(inner) => inner.search(key, depth),
        }
    }

    fn insert(&mut self, key: K, value: V, depth: usize) {
        match self {
            Self::Leaf(leaf) => {
                let (partial, k_new, k_old) = {
                    let new_key_bytes = key.bytes();
                    if leaf.match_key(new_key_bytes.as_ref()) {
                        // Inserting an existing key.
                        leaf.value = value;
                        return;
                    }
                    // Determines the partial key for the new node and the keys for the two children.
                    let old_key_bytes = leaf.key.bytes();
                    let prefix_len = longest_common_prefix(
                        new_key_bytes.as_ref(),
                        old_key_bytes.as_ref(),
                        depth,
                    );
                    let new_depth = depth + prefix_len;
                    (
                        PartialKey::new(&new_key_bytes.as_ref()[depth..], prefix_len),
                        byte_at(new_key_bytes.as_ref(), new_depth),
                        byte_at(old_key_bytes.as_ref(), new_depth),
                    )
                };
                // Replace the current node, then add the old leaf and new leaf as its children.
                let new_leaf = Self::new_leaf(key, value);
                let old_leaf = std::mem::replace(self, Self::new_internal(partial));
                self.add_child(k_new, new_leaf);
                self.add_child(k_old, old_leaf);
            }
            Self::Inner(inner) => {
                if inner.partial.len > 0 {
                    let (prefix_diff, byte_key) = {
                        let key_bytes = key.bytes();
                        let prefix_diff = inner.prefix_mismatch(key_bytes.as_ref(), depth);
                        (
                            prefix_diff,
                            byte_at(key_bytes.as_ref(), depth + prefix_diff),
                        )
                    };
                    if prefix_diff < inner.partial.len {
                        let shift = prefix_diff + 1;
                        let partial = PartialKey::new(&inner.partial.data, prefix_diff);
                        if inner.partial.len <= P {
                            let byte_key = byte_at(&inner.partial.data, prefix_diff);
                            inner.partial.len -= shift;
                            inner.partial.data.copy_within(shift.., 0);
                            let old_node = std::mem::replace(self, Self::new_internal(partial));
                            self.add_child(byte_key, old_node);
                        } else if let Some(leaf) = inner.indices.min_leaf() {
                            let byte_key = {
                                let leaf_key_bytes = leaf.key.bytes();
                                let offset = depth + shift;
                                let partial_len = min(P, inner.partial.len);
                                inner.partial.len -= shift;
                                inner.partial.data[..partial_len].copy_from_slice(
                                    &leaf_key_bytes.as_ref()[offset..offset + partial_len],
                                );
                                byte_at(leaf_key_bytes.as_ref(), depth + prefix_diff)
                            };
                            let old_node = std::mem::replace(self, Self::new_internal(partial));
                            self.add_child(byte_key, old_node);
                        }
                        let leaf = Self::new_leaf(key, value);
                        self.add_child(byte_key, leaf);
                    } else {
                        inner.insert(key, value, depth + inner.partial.len);
                    }
                } else {
                    inner.insert(key, value, depth);
                }
            }
        }
    }

    fn delete(&mut self, key: &[u8], depth: usize) -> Option<Self> {
        let Self::Inner(inner) = self else {
            return None;
        };
        // The key doesn't match the prefix partial.
        if !inner.partial.match_key(key, depth) {
            return None;
        }
        // Find the child node corresponding to the key.
        let depth = depth + inner.partial.len;
        let child_key = byte_at(key, depth);
        let Some(child) = inner.child_mut(child_key) else {
            return None;
        };
        // Do recursion if the child is an internal node.
        let Self::Leaf(leaf) = child else {
            return child.delete(key, depth + 1);
        };
        // The leaf's key doesn't match.
        if !leaf.match_key(key) {
            return None;
        }
        let deleted_node = inner.del_child(child_key);
        if let Some(node) = inner.shrink() {
            *self = node;
        }
        deleted_node
    }

    fn add_child(&mut self, key: u8, child: Self) {
        if let Self::Inner(inner) = self {
            inner.add_child(key, child);
        };
    }
}

impl<K, V, const P: usize> Node<K, V, P>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn debug_print_node(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        key: u8,
        level: usize,
    ) -> std::fmt::Result {
        for _ in 0..level {
            write!(f, "  ")?;
        }
        match self {
            Self::Leaf(leaf) => {
                writeln!(f, "[{:03}] leaf: {:?} -> {:?}", key, leaf.key, leaf.value)?;
            }
            Self::Inner(inner) => match &inner.indices {
                InnerIndices::Node4(indices) => {
                    writeln!(f, "[{:03}] node4 {:?}", key, inner.partial)?;
                    for (key, child) in indices.as_ref() {
                        child.debug_print_node(f, key, level + 1)?;
                    }
                }
                InnerIndices::Node16(indices) => {
                    writeln!(f, "[{:03}] node16 {:?}", key, inner.partial)?;
                    for (key, child) in indices.as_ref() {
                        child.debug_print_node(f, key, level + 1)?;
                    }
                }
                InnerIndices::Node48(indices) => {
                    writeln!(f, "[{:03}] node48 {:?}", key, inner.partial)?;
                    for (key, child) in indices.as_ref() {
                        child.debug_print_node(f, key, level + 1)?;
                    }
                }
                InnerIndices::Node256(indices) => {
                    writeln!(f, "[{:03}] node256 {:?}", key, inner.partial)?;
                    for (key, child) in indices.as_ref() {
                        child.debug_print_node(f, key, level + 1)?;
                    }
                }
            },
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct Leaf<K, V> {
    key: K,
    value: V,
}

impl<K, V> Leaf<K, V>
where
    K: BytesComparable,
{
    fn match_key(&self, key: &[u8]) -> bool {
        self.key.bytes().as_ref() == key
    }
}

#[derive(Debug)]
struct Inner<K, V, const P: usize> {
    partial: PartialKey<P>,
    indices: InnerIndices<K, V, P>,
}

impl<K, V, const P: usize> Inner<K, V, P> {
    fn new(partial: PartialKey<P>) -> Self {
        Self {
            partial,
            indices: InnerIndices::Node4(Box::default()),
        }
    }
}

impl<K, V, const P: usize> Inner<K, V, P>
where
    K: BytesComparable,
{
    fn search(&self, key: &[u8], depth: usize) -> Option<&Leaf<K, V>> {
        if !self.partial.match_key(key, depth) {
            return None;
        }
        let next_depth = depth + self.partial.len;
        let byte_key = byte_at(key, next_depth);
        self.child_ref(byte_key)
            .and_then(|child| child.search(key, next_depth + 1))
    }

    fn insert(&mut self, key: K, value: V, depth: usize) {
        let byte_key = byte_at(key.bytes().as_ref(), depth);
        if let Some(child) = self.child_mut(byte_key) {
            child.insert(key, value, depth + 1);
        } else {
            let leaf = Node::new_leaf(key, value);
            self.add_child(byte_key, leaf);
        }
    }

    fn add_child(&mut self, key: u8, child: Node<K, V, P>) {
        self.grow();
        match &mut self.indices {
            InnerIndices::Node4(indices) => indices.add_child(key, child),
            InnerIndices::Node16(indices) => indices.add_child(key, child),
            InnerIndices::Node48(indices) => indices.add_child(key, child),
            InnerIndices::Node256(indices) => indices.add_child(key, child),
        }
    }

    fn del_child(&mut self, key: u8) -> Option<Node<K, V, P>> {
        match &mut self.indices {
            InnerIndices::Node4(indices) => indices.del_child(key),
            InnerIndices::Node16(indices) => indices.del_child(key),
            InnerIndices::Node48(indices) => indices.del_child(key),
            InnerIndices::Node256(indices) => indices.del_child(key),
        }
    }

    fn child_ref(&self, key: u8) -> Option<&Node<K, V, P>> {
        match &self.indices {
            InnerIndices::Node4(indices) => indices.child_ref(key),
            InnerIndices::Node16(indices) => indices.child_ref(key),
            InnerIndices::Node48(indices) => indices.child_ref(key),
            InnerIndices::Node256(indices) => indices.child_ref(key),
        }
    }

    fn child_mut(&mut self, key: u8) -> Option<&mut Node<K, V, P>> {
        match &mut self.indices {
            InnerIndices::Node4(indices) => indices.child_mut(key),
            InnerIndices::Node16(indices) => indices.child_mut(key),
            InnerIndices::Node48(indices) => indices.child_mut(key),
            InnerIndices::Node256(indices) => indices.child_mut(key),
        }
    }

    fn grow(&mut self) {
        match &mut self.indices {
            InnerIndices::Node4(indices) => {
                if indices.is_full() {
                    let mut new_indices = Sorted::<Node<K, V, P>, 16>::default();
                    new_indices.consume_sorted(indices);
                    self.indices = InnerIndices::Node16(Box::new(new_indices));
                }
            }
            InnerIndices::Node16(indices) => {
                if indices.is_full() {
                    let mut new_indices = Indirect::<Node<K, V, P>, 48>::default();
                    new_indices.consume_sorted(indices);
                    self.indices = InnerIndices::Node48(Box::new(new_indices));
                }
            }
            InnerIndices::Node48(indices) => {
                if indices.is_full() {
                    let mut new_indices = Direct::<Node<K, V, P>>::default();
                    new_indices.consume_indirect(indices);
                    self.indices = InnerIndices::Node256(Box::new(new_indices));
                }
            }
            InnerIndices::Node256(_) => {}
        }
    }

    fn shrink(&mut self) -> Option<Node<K, V, P>> {
        match &mut self.indices {
            InnerIndices::Node4(indices) => {
                if let Some((sub_child_key, mut sub_child)) = indices.release() {
                    if let Node::Inner(sub_child) = &mut sub_child {
                        self.partial.push(sub_child_key);
                        self.partial.append(&sub_child.partial);
                        std::mem::swap(&mut self.partial, &mut sub_child.partial);
                    }
                    return Some(sub_child);
                }
            }
            InnerIndices::Node16(indices) => {
                if indices.len() < 4 {
                    let mut new_indices = Sorted::<Node<K, V, P>, 4>::default();
                    new_indices.consume_sorted(indices);
                    self.indices = InnerIndices::Node4(Box::new(new_indices));
                }
            }
            InnerIndices::Node48(indices) => {
                if indices.len() < 16 {
                    let mut new_indices = Sorted::<Node<K, V, P>, 16>::default();
                    new_indices.consume_indirect(indices);
                    self.indices = InnerIndices::Node16(Box::new(new_indices));
                }
            }
            InnerIndices::Node256(indices) => {
                if indices.len() < 48 {
                    let mut new_indices = Indirect::<Node<K, V, P>, 48>::default();
                    new_indices.consume_direct(indices);
                    self.indices = InnerIndices::Node48(Box::new(new_indices));
                }
            }
        }
        None
    }

    fn prefix_mismatch(&self, key: &[u8], depth: usize) -> usize {
        let len = min(P, self.partial.len);
        let mut idx = 0;
        for (l, r) in self.partial.data[..len].iter().zip(key[depth..].iter()) {
            if l != r {
                return idx;
            }
            idx += 1;
        }
        // If the prefix is short so we don't have to check a leaf.
        if self.partial.len > P {
            if let Some(leaf) = self.indices.min_leaf() {
                idx += longest_common_prefix(leaf.key.bytes().as_ref(), key, depth + idx);
            }
        }
        idx
    }
}

#[derive(Debug)]
enum InnerIndices<K, V, const P: usize> {
    Node4(Box<Sorted<Node<K, V, P>, 4>>),
    Node16(Box<Sorted<Node<K, V, P>, 16>>),
    Node48(Box<Indirect<Node<K, V, P>, 48>>),
    Node256(Box<Direct<Node<K, V, P>>>),
}

impl<K, V, const P: usize> InnerIndices<K, V, P> {
    fn min_leaf(&self) -> Option<&Leaf<K, V>> {
        match self {
            Self::Node4(indices) => indices.min(),
            Self::Node16(indices) => indices.min(),
            Self::Node48(indices) => indices.min(),
            Self::Node256(indices) => indices.min(),
        }
        .and_then(|child| match child {
            Node::Leaf(leaf) => Some(leaf.as_ref()),
            Node::Inner(inner) => inner.indices.min_leaf(),
        })
    }

    fn max_leaf(&self) -> Option<&Leaf<K, V>> {
        match self {
            Self::Node4(indices) => indices.max(),
            Self::Node16(indices) => indices.max(),
            Self::Node48(indices) => indices.max(),
            Self::Node256(indices) => indices.max(),
        }
        .and_then(|child| match child {
            Node::Leaf(leaf) => Some(leaf.as_ref()),
            Node::Inner(inner) => inner.indices.max_leaf(),
        })
    }
}

#[derive(Debug, Clone)]
struct PartialKey<const N: usize> {
    len: usize,
    data: [u8; N],
}

impl<const N: usize> PartialKey<N> {
    fn new(key: &[u8], len: usize) -> Self {
        let partial_len = min(N, len);
        let mut data = [0; N];
        data[..partial_len].copy_from_slice(&key[..partial_len]);
        Self { len, data }
    }

    fn push(&mut self, char: u8) {
        if self.len < N {
            self.data[self.len] = char;
        }
        self.len += 1;
    }

    fn append(&mut self, other: &Self) {
        if self.len < N {
            let len = min(other.len, N - self.len);
            self.data[self.len..self.len + len].copy_from_slice(&other.data[..len]);
        }
        self.len += other.len;
    }

    fn match_key(&self, key: &[u8], depth: usize) -> bool {
        let partial_len = min(N, self.len);
        self.data[..partial_len]
            .iter()
            .zip(key[depth..].iter())
            .take_while(|(x, y)| x.eq(y))
            .count()
            .eq(&partial_len)
    }
}

impl BytesComparable for u8 {
    type Target<'a> = [Self; 1];

    fn bytes(&self) -> Self::Target<'static> {
        self.to_be_bytes()
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
        let flipped = self ^ (1 << 7);
        flipped.to_be_bytes()
    }
}

impl BytesComparable for i16 {
    type Target<'a> = [u8; 2];

    fn bytes(&self) -> Self::Target<'static> {
        let flipped = self ^ (1 << 15);
        flipped.to_be_bytes()
    }
}

impl BytesComparable for i32 {
    type Target<'a> = [u8; 4];

    fn bytes(&self) -> Self::Target<'static> {
        let flipped = self ^ (1 << 31);
        flipped.to_be_bytes()
    }
}

impl BytesComparable for i64 {
    type Target<'a> = [u8; 8];

    fn bytes(&self) -> Self::Target<'static> {
        let flipped = self ^ (1 << 63);
        flipped.to_be_bytes()
    }
}

impl BytesComparable for i128 {
    type Target<'a> = [u8; 16];

    fn bytes(&self) -> Self::Target<'static> {
        let flipped = self ^ (1 << 127);
        flipped.to_be_bytes()
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

/// Count the number of matching elements at the beginning of two slices.
fn longest_common_prefix<T>(lhs: &[T], rhs: &[T], depth: usize) -> usize
where
    T: PartialEq,
{
    lhs[depth..]
        .iter()
        .zip(rhs[depth..].iter())
        .take_while(|(x, y)| x == y)
        .count()
}

fn byte_at(bytes: &[u8], pos: usize) -> u8 {
    bytes.get(pos).copied().unwrap_or(0)
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
        let mut tree = Tree::default();
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
