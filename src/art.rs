//! # Adaptive Radix Tree.

use std::{borrow::Borrow, cmp::min};

use crate::indices::{self, Indices};

/// An adaptive radix tree. This structure contains the root node of the tree and serves as the
/// entrypoint for all tree operations.
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
            debug_print_node(f, root, 0, 0)
        } else {
            writeln!(f, "empty")
        }
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
        self.root.as_ref().and_then(|node| node.search(key))
    }

    /// Insert the given key-value pair into the tree.
    pub fn insert(&mut self, key: K, value: V) {
        if let Some(ref mut root) = self.root {
            root.insert(key, value, 0);
        } else {
            self.root.replace(Node::new_leaf(key, value));
        }
    }

    /// Find the minimum key-value pair in the tree.
    #[must_use]
    pub fn min(&self) -> Option<(&K, &V)> {
        self.root.as_ref().and_then(|root| match root {
            Node::Leaf(leaf) => Some((&leaf.key, &leaf.value)),
            Node::Internal(node) => node.indices.min_leaf().map(|leaf| (&leaf.key, &leaf.value)),
        })
    }

    /// Find the maximum key-value pair in the tree.
    #[must_use]
    pub fn max(&self) -> Option<(&K, &V)> {
        self.root.as_ref().and_then(|root| match root {
            Node::Leaf(leaf) => Some((&leaf.key, &leaf.value)),
            Node::Internal(node) => node.indices.max_leaf().map(|leaf| (&leaf.key, &leaf.value)),
        })
    }
}

#[derive(Debug)]
enum Node<K, V, const P: usize> {
    Leaf(Box<Leaf<K, V>>),
    Internal(Internal<K, V, P>),
}

impl<K, V, const P: usize> Node<K, V, P> {
    fn new_leaf(key: K, value: V) -> Self {
        Self::Leaf(Box::new(Leaf { key, value }))
    }

    fn new_internal(partial: PartialKey<P>) -> Self {
        Self::Internal(Internal::new(partial))
    }

    fn add_child(&mut self, key: u8, child: Self) {
        match self {
            Self::Internal(node) => node.indices.add_child(key, child),
            Self::Leaf(_) => unreachable!("[bug] can't add child to leaf"),
        }
    }
}

impl<K, V, const P: usize> Node<K, V, P>
where
    K: BytesComparable,
{
    fn search<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: BytesComparable + ?Sized,
    {
        let key_bytes = key.bytes();
        self.search_recursive(key_bytes.as_ref(), 0)
    }

    fn search_recursive(&self, key: &[u8], depth: usize) -> Option<&V> {
        match self {
            Self::Leaf(node) => {
                if !node.match_key(key) {
                    return None;
                }
                Some(&node.value)
            }
            Self::Internal(node) => node.search_child(key, depth),
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
            Self::Internal(node) => {
                if node.partial.len > 0 {
                    let (prefix_diff, byte_key) = {
                        let key_bytes = key.bytes();
                        let prefix_diff = node.prefix_mismatch(key_bytes.as_ref(), depth);
                        (
                            prefix_diff,
                            byte_at(key_bytes.as_ref(), depth + prefix_diff),
                        )
                    };
                    if prefix_diff < node.partial.len {
                        let shift = prefix_diff + 1;
                        let partial = PartialKey::new(&node.partial.data, prefix_diff);
                        if node.partial.len <= P {
                            let byte_key = byte_at(&node.partial.data, prefix_diff);
                            node.partial.len -= shift;
                            node.partial.data.copy_within(shift.., 0);
                            let old_node = std::mem::replace(self, Self::new_internal(partial));
                            self.add_child(byte_key, old_node);
                        } else {
                            let leaf = node
                                .indices
                                .min_leaf()
                                .expect("[bug] there must be a min leaf");
                            let byte_key = {
                                let leaf_key_bytes = leaf.key.bytes();
                                let offset = depth + shift;
                                let partial_len = min(P, node.partial.len);
                                node.partial.len -= shift;
                                node.partial.data[..partial_len].copy_from_slice(
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
                        Self::insert_child(node, key, value, depth + node.partial.len);
                    }
                } else {
                    Self::insert_child(node, key, value, depth);
                }
            }
        }
    }

    fn insert_child(node: &mut Internal<K, V, P>, key: K, value: V, depth: usize) {
        let byte_key = {
            let key_bytes = key.bytes();
            byte_at(key_bytes.as_ref(), depth)
        };
        if let Some(child) = node.indices.child_mut(byte_key) {
            child.insert(key, value, depth + 1);
        } else {
            let leaf = Self::new_leaf(key, value);
            node.indices.add_child(byte_key, leaf);
        }
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
struct Internal<K, V, const P: usize> {
    partial: PartialKey<P>,
    indices: InternalIndices<K, V, P>,
}

impl<K, V, const P: usize> Internal<K, V, P> {
    fn new(partial: PartialKey<P>) -> Self {
        Self {
            partial,
            indices: InternalIndices::Node4(Box::default()),
        }
    }
}

impl<K, V, const P: usize> Internal<K, V, P>
where
    K: BytesComparable,
{
    fn search_child(&self, key: &[u8], depth: usize) -> Option<&V> {
        if !self.partial.match_key(key, depth) {
            return None;
        }
        let next_depth = depth + self.partial.len;
        let byte_key = byte_at(key, next_depth);
        let child = match &self.indices {
            InternalIndices::Node4(node) => node.child_ref(byte_key),
            InternalIndices::Node16(node) => node.child_ref(byte_key),
            InternalIndices::Node48(node) => node.child_ref(byte_key),
            InternalIndices::Node256(node) => node.child_ref(byte_key),
        };
        child.and_then(|child| child.search_recursive(key, next_depth + 1))
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
            let leaf = self
                .indices
                .min_leaf()
                .expect("[bug] there must be a min leaf");

            let leaf_key_bytes = leaf.key.bytes();
            idx += longest_common_prefix(leaf_key_bytes.as_ref(), key, depth + idx);
        }
        idx
    }
}

#[derive(Debug)]
enum InternalIndices<K, V, const P: usize> {
    Node4(Box<indices::Sorted<Node<K, V, P>, 4>>),
    Node16(Box<indices::Sorted<Node<K, V, P>, 16>>),
    Node48(Box<indices::Indirect<Node<K, V, P>, 48>>),
    Node256(Box<indices::Direct<Node<K, V, P>>>),
}

impl<K, V, const P: usize> InternalIndices<K, V, P> {
    fn add_child(&mut self, key: u8, child: Node<K, V, P>) {
        if self.is_full() {
            self.grow();
        }
        match self {
            Self::Node4(node) => node.add_child(key, child),
            Self::Node16(node) => node.add_child(key, child),
            Self::Node48(node) => node.add_child(key, child),
            Self::Node256(node) => node.add_child(key, child),
        }
    }

    fn is_full(&self) -> bool {
        match self {
            Self::Node4(node) => node.is_full(),
            Self::Node16(node) => node.is_full(),
            Self::Node48(node) => node.is_full(),
            Self::Node256(_) => false,
        }
    }

    fn grow(&mut self) {
        match self {
            Self::Node4(node) => {
                let mut new_indices = indices::Sorted::<Node<K, V, P>, 16>::default();
                new_indices.consume_sorted(node);
                let _ = std::mem::replace(self, Self::Node16(Box::new(new_indices)));
            }
            Self::Node16(node) => {
                let mut new_indices = indices::Indirect::<Node<K, V, P>, 48>::default();
                new_indices.consume_sorted(node);
                let _ = std::mem::replace(self, Self::Node48(Box::new(new_indices)));
            }
            Self::Node48(node) => {
                let mut new_indices = indices::Direct::<Node<K, V, P>>::default();
                new_indices.consume_indirect(node);
                let _ = std::mem::replace(self, Self::Node256(Box::new(new_indices)));
            }
            Self::Node256(_) => unreachable!("[bug] can't grow node256"),
        }
    }

    fn child_mut(&mut self, key: u8) -> Option<&mut Node<K, V, P>> {
        match self {
            Self::Node4(node) => node.child_mut(key),
            Self::Node16(node) => node.child_mut(key),
            Self::Node48(node) => node.child_mut(key),
            Self::Node256(node) => node.child_mut(key),
        }
    }

    fn min_leaf(&self) -> Option<&Leaf<K, V>> {
        let child = match self {
            Self::Node4(indices) => indices.min(),
            Self::Node16(indices) => indices.min(),
            Self::Node48(indices) => indices.min(),
            Self::Node256(indices) => indices.min(),
        };
        child.and_then(|child| match child {
            Node::Leaf(leaf) => Some(leaf.as_ref()),
            Node::Internal(node) => node.indices.min_leaf(),
        })
    }

    fn max_leaf(&self) -> Option<&Leaf<K, V>> {
        let child = match self {
            Self::Node4(indices) => indices.max(),
            Self::Node16(indices) => indices.max(),
            Self::Node48(indices) => indices.max(),
            Self::Node256(indices) => indices.max(),
        };
        child.and_then(|child| match child {
            Node::Leaf(leaf) => Some(leaf.as_ref()),
            Node::Internal(node) => node.indices.max_leaf(),
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
}

impl<const N: usize> PartialKey<N> {
    fn match_key(&self, key: &[u8], depth: usize) -> bool {
        let partial_len = min(N, self.len);
        let common_prefix_len = self.data[..partial_len]
            .iter()
            .zip(key[depth..].iter())
            .take_while(|(x, y)| x.eq(y))
            .count();

        common_prefix_len == partial_len
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

fn debug_print_indentation(
    formatter: &mut std::fmt::Formatter<'_>,
    level: usize,
) -> std::fmt::Result {
    for _ in 0..level {
        write!(formatter, "  ")?;
    }
    Ok(())
}

fn debug_print_node<K, V, const P: usize>(
    f: &mut std::fmt::Formatter<'_>,
    node: &Node<K, V, P>,
    key: u8,
    level: usize,
) -> std::fmt::Result
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    debug_print_indentation(f, level)?;
    match node {
        Node::Leaf(leaf) => {
            writeln!(f, "[{:03}] leaf: {:?} -> {:?}", key, leaf.key, leaf.value)?;
        }
        Node::Internal(node) => match &node.indices {
            InternalIndices::Node4(indices) => {
                writeln!(f, "[{:03}] node4 {:?}", key, node.partial)?;
                for (key, child) in indices.as_ref() {
                    debug_print_node(f, child, key, level + 1)?;
                }
            }
            InternalIndices::Node16(indices) => {
                writeln!(f, "[{:03}] node16 {:?}", key, node.partial)?;
                for (key, child) in indices.as_ref() {
                    debug_print_node(f, child, key, level + 1)?;
                }
            }
            InternalIndices::Node48(indices) => {
                writeln!(f, "[{:03}] node48 {:?}", key, node.partial)?;
                for (key, child) in indices.as_ref() {
                    debug_print_node(f, child, key, level + 1)?;
                }
            }
            InternalIndices::Node256(indices) => {
                writeln!(f, "[{:03}] node256 {:?}", key, node.partial)?;
                for (key, child) in indices.as_ref() {
                    debug_print_node(f, child, key, level + 1)?;
                }
            }
        },
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::Tree;

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
}
