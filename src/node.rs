use std::cmp::min;

use crate::{
    indices::{Indices, Indices16, Indices256, Indices4, Indices48},
    BytesComparable,
};

/// A node in the ART tree, which can be either an inner node or a leaf node. Leaf nodes hold data of
/// key-value pairs, and inner nodes holds indices to its children.
#[derive(Debug)]
pub enum Node<K, V, const P: usize> {
    Leaf(Leaf<K, V>),
    Inner(Inner<K, V, P>),
}

impl<K, V, const P: usize> Node<K, V, P> {
    /// Create a new leaf node.
    pub const fn new_leaf(key: K, value: V) -> Self {
        Self::Leaf(Leaf { key, value })
    }

    /// Create a new inner node.
    fn new_inner(partial: PartialKey<P>) -> Self {
        Self::Inner(Inner::new(partial))
    }
}

impl<K, V, const P: usize> Node<K, V, P>
where
    K: BytesComparable,
{
    /// Finds the leaf node that matches the given key.
    ///
    /// # Arguments
    ///
    /// - `key`: The key to search for.
    /// - `depth`: The number of bytes in the key to skip. This number increases as we go deeper into the tree
    /// and depends on the length of prefixes along the path.
    pub fn search(&self, key: &[u8], depth: usize) -> Option<&Leaf<K, V>> {
        match &self {
            Self::Leaf(leaf) => {
                if !leaf.match_key(key) {
                    return None;
                }
                Some(leaf)
            }
            Self::Inner(inner) => inner.search_recursive(key, depth),
        }
    }

    /// Inserts the given key-value pair into the node.
    ///
    /// # Arguments
    ///
    /// - `key`: The key to insert.
    /// - `value`: The value to insert.
    /// - `depth`: The number of bytes in the key to skip. This number increases as we go deeper into the tree
    /// and depends on the length of prefixes along the path.
    pub fn insert(&mut self, key: K, value: V, depth: usize) {
        match self {
            Self::Leaf(leaf) => {
                // Here we create a scope to avoid borrowing `key` for too long in order to move it into the new leaf.
                let (partial, k_new, k_old) = {
                    let new_key_bytes = key.bytes();
                    // If the leaf's key matches the new key, then update it's value and return early.
                    if leaf.match_key(new_key_bytes.as_ref()) {
                        leaf.value = value;
                        return;
                    }
                    // Calculates the common prefix length between the new key and the leaf's key.
                    let old_key_bytes = leaf.key.bytes();
                    let prefix_len = longest_common_prefix(
                        new_key_bytes.as_ref(),
                        old_key_bytes.as_ref(),
                        depth,
                    );
                    // Creates a new partial key from the common prefix. Then gets the new and old byte keys of where
                    // the leaves are placed within the inner node.
                    let new_depth = depth + prefix_len;
                    (
                        PartialKey::new(&new_key_bytes.as_ref()[depth..], prefix_len),
                        byte_at(new_key_bytes.as_ref(), new_depth),
                        byte_at(old_key_bytes.as_ref(), new_depth),
                    )
                };
                // Replace the current node, then add the old leaf and new leaf as its children.
                let new_leaf = Self::new_leaf(key, value);
                let old_leaf = std::mem::replace(self, Self::new_inner(partial));
                self.add_child(k_new, new_leaf);
                self.add_child(k_old, old_leaf);
            }
            Self::Inner(inner) => {
                // Inner node has no prefix, insert recursively into it without any checks or modifications.
                if inner.partial.len == 0 {
                    return inner.insert_recursive(key, value, depth);
                }
                // Find the index at which the new key differs from the inner node's partial key.
                let (prefix_diff, new_byte_key) = {
                    let key_bytes = key.bytes();
                    let prefix_diff = inner.first_mismatch_index(key_bytes.as_ref(), depth);
                    let byte_key = byte_at(key_bytes.as_ref(), depth + prefix_diff);
                    (prefix_diff, byte_key)
                };
                // The index at which the new key differs is not covered by the current partial key,
                // so we insert recursively.
                if prefix_diff >= inner.partial.len {
                    return inner.insert_recursive(key, value, depth + inner.partial.len);
                }
                // At this point, we found a difference between the new key and the inner node's partial key.
                let shift = prefix_diff + 1;
                let partial = PartialKey::new(&inner.partial.data, prefix_diff);
                if inner.partial.len <= P {
                    // The mismatched byte is contained within the partial key data. We modify the inner node
                    // partial key by skipping the common prefix plus the first byte where the keys differ.
                    // A new inner node is created, and we add the old inner node as its child.
                    let byte_key = byte_at(&inner.partial.data, prefix_diff);
                    inner.partial.len -= shift;
                    inner.partial.data.copy_within(shift.., 0);
                    let old_node = std::mem::replace(self, Self::new_inner(partial));
                    self.add_child(byte_key, old_node);
                } else {
                    let Some(leaf) = inner.indices.min_leaf_recursive() else {
                        unreachable!(
                            "a leaf must exist in the tree if the prefix is longer than the partial key"
                        )
                    };
                    // The mismatched byte is contained outside of the partial key data. We modify the inner node
                    // by filling its partial key data with part of the common prefix copied from the minimum leaf's
                    // key. A new inner node is created, and we add the old inner node as its child.
                    let byte_key = {
                        let leaf_key_bytes = leaf.key.bytes();
                        let offset = depth + shift;
                        inner.partial.len -= shift;
                        inner.partial.data[..P]
                            .copy_from_slice(&leaf_key_bytes.as_ref()[offset..offset + P]);
                        byte_at(leaf_key_bytes.as_ref(), depth + prefix_diff)
                    };
                    let old_node = std::mem::replace(self, Self::new_inner(partial));
                    self.add_child(byte_key, old_node);
                }
                self.add_child(new_byte_key, Self::new_leaf(key, value));
            }
        }
    }

    pub fn delete(&mut self, key: &[u8], depth: usize) -> Option<Leaf<K, V>> {
        let Self::Inner(inner) = self else {
            unreachable!("can not call delete on a leaf node");
        };
        let deleted = inner.delete_recursive(key, depth);
        if let Some(node) = inner.shrink() {
            *self = node;
        }
        deleted
    }

    pub fn min_leaf(&self) -> Option<&Leaf<K, V>> {
        match self {
            Self::Leaf(leaf) => Some(leaf),
            Self::Inner(inner) => inner.indices.min_leaf_recursive(),
        }
    }

    pub fn max_leaf(&self) -> Option<&Leaf<K, V>> {
        match self {
            Self::Leaf(leaf) => Some(leaf),
            Self::Inner(inner) => inner.indices.max_leaf_recursive(),
        }
    }

    fn add_child(&mut self, key: u8, child: Self) {
        // NOTE: Is there a way to avoid this match?
        let Self::Inner(inner) = self else {
            unreachable!("can not add child on a leaf node")
        };
        inner.add_child(key, child);
    }
}

pub fn debug_print<K, V, const P: usize>(
    f: &mut std::fmt::Formatter<'_>,
    node: &Node<K, V, P>,
    key: u8,
    level: usize,
) -> std::fmt::Result
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    for _ in 0..level {
        write!(f, "  ")?;
    }
    match node {
        Node::Leaf(leaf) => {
            writeln!(f, "[{:03}] leaf: {:?} -> {:?}", key, leaf.key, leaf.value)?;
        }
        Node::Inner(inner) => match &inner.indices {
            InnerIndices::Node4(indices) => {
                writeln!(f, "[{:03}] node4 {:?}", key, inner.partial)?;
                for (key, child) in indices {
                    debug_print(f, child, key, level + 1)?;
                }
            }
            InnerIndices::Node16(indices) => {
                writeln!(f, "[{:03}] node16 {:?}", key, inner.partial)?;
                for (key, child) in indices {
                    debug_print(f, child, key, level + 1)?;
                }
            }
            InnerIndices::Node48(indices) => {
                writeln!(f, "[{:03}] node48 {:?}", key, inner.partial)?;
                for (key, child) in indices {
                    debug_print(f, child, key, level + 1)?;
                }
            }
            InnerIndices::Node256(indices) => {
                writeln!(f, "[{:03}] node256 {:?}", key, inner.partial)?;
                for (key, child) in indices {
                    debug_print(f, child, key, level + 1)?;
                }
            }
        },
    }
    Ok(())
}

/// Count the number of common elements at the beginning of two slices.
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

/// Gets the byte at the given position in the slice. If it is out of bounds, then 0 is returned.
fn byte_at(bytes: &[u8], pos: usize) -> u8 {
    bytes.get(pos).copied().unwrap_or(0)
}

#[derive(Debug, Clone)]
pub struct Leaf<K, V> {
    pub key: K,
    pub value: V,
}

impl<K, V> Leaf<K, V>
where
    K: BytesComparable,
{
    /// Check if the key of the leaf exactly matches the given key.
    pub fn match_key(&self, key: &[u8]) -> bool {
        self.key.bytes().as_ref() == key
    }
}

#[derive(Debug)]
pub struct Inner<K, V, const P: usize> {
    partial: PartialKey<P>,
    indices: InnerIndices<K, V, P>,
}

impl<K, V, const P: usize> Inner<K, V, P> {
    fn new(partial: PartialKey<P>) -> Self {
        Self {
            partial,
            indices: InnerIndices::Node4(Indices4::default()),
        }
    }
}

impl<K, V, const P: usize> Inner<K, V, P>
where
    K: BytesComparable,
{
    fn search_recursive(&self, key: &[u8], depth: usize) -> Option<&Leaf<K, V>> {
        if !self.partial.match_key(key, depth) {
            return None;
        }
        let next_depth = depth + self.partial.len;
        let byte_key = byte_at(key, next_depth);
        self.child_ref(byte_key)
            .and_then(|child| child.search(key, next_depth + 1))
    }

    fn insert_recursive(&mut self, key: K, value: V, depth: usize) {
        let byte_key = byte_at(key.bytes().as_ref(), depth);
        if let Some(child) = self.child_mut(byte_key) {
            // Found a child so we recursively insert into it.
            child.insert(key, value, depth + 1);
        } else {
            // No child found so we insert a new leaf into the current node.
            let leaf = Node::new_leaf(key, value);
            self.add_child(byte_key, leaf);
        }
    }

    fn delete_recursive(&mut self, key: &[u8], depth: usize) -> Option<Leaf<K, V>> {
        // The key doesn't match the prefix partial.
        if !self.partial.match_key(key, depth) {
            return None;
        }
        // Find the child node corresponding to the key.
        let depth = depth + self.partial.len;
        let child_key = byte_at(key, depth);
        let Some(child) = self.child_mut(child_key) else {
            return None;
        };
        // Do recursion if the child is an inner node.
        match child {
            Node::Leaf(leaf) => {
                // The leaf's key doesn't match.
                if !leaf.match_key(key) {
                    return None;
                }
                self.del_child(child_key).map(|child| {
                    let Node::Leaf(leaf) = child else {
                        unreachable!("must be a leaf because we just perform a match above with the same key")
                    };
                    leaf
                })
            }
            Node::Inner(inner) => {
                let deleted = inner.delete_recursive(key, depth + 1);
                if let Some(node) = inner.shrink() {
                    *child = node;
                }
                deleted
            }
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
                    self.indices = InnerIndices::Node16(Indices16::<Node<K, V, P>>::from(indices));
                }
            }
            InnerIndices::Node16(indices) => {
                if indices.is_full() {
                    self.indices = InnerIndices::Node48(Indices48::<Node<K, V, P>>::from(indices));
                }
            }
            InnerIndices::Node48(indices) => {
                if indices.is_full() {
                    self.indices =
                        InnerIndices::Node256(Indices256::<Node<K, V, P>>::from(indices));
                }
            }
            InnerIndices::Node256(_) => {}
        }
    }

    fn shrink(&mut self) -> Option<Node<K, V, P>> {
        match &mut self.indices {
            InnerIndices::Node4(indices) => {
                if indices.len() <= 1 {
                    let (sub_child_key, mut sub_child) = indices.free();
                    if let Node::Inner(sub_child) = &mut sub_child {
                        self.partial.push(sub_child_key);
                        self.partial.append(&sub_child.partial);
                        std::mem::swap(&mut self.partial, &mut sub_child.partial);
                    }
                    return Some(sub_child);
                }
            }
            InnerIndices::Node16(indices) => {
                if indices.len() <= 3 {
                    self.indices = InnerIndices::Node4(Indices4::from(indices));
                }
            }
            InnerIndices::Node48(indices) => {
                if indices.len() <= 12 {
                    self.indices = InnerIndices::Node16(Indices16::from(indices));
                }
            }
            InnerIndices::Node256(indices) => {
                if indices.len() <= 37 {
                    self.indices = InnerIndices::Node48(Indices48::from(indices));
                }
            }
        }
        None
    }

    fn first_mismatch_index(&self, key: &[u8], depth: usize) -> usize {
        let len = min(P, self.partial.len);
        let mut idx = 0;
        for (l, r) in self.partial.data[..len].iter().zip(key[depth..].iter()) {
            if l != r {
                return idx;
            }
            idx += 1;
        }
        if self.partial.len > P {
            // Prefix is longer than what we've checked, find a leaf. The minimum leaf is
            // guaranteed to contains the longest common prefix of the current partial key.
            let Some(leaf) = self.indices.min_leaf_recursive() else {
                unreachable!(
                    "a leaf must exist in the tree if the prefix is longer than the partial key"
                )
            };
            idx += longest_common_prefix(leaf.key.bytes().as_ref(), key, depth + idx);
        }
        idx
    }
}

#[derive(Debug)]
enum InnerIndices<K, V, const P: usize> {
    Node4(Indices4<Node<K, V, P>>),
    Node16(Indices16<Node<K, V, P>>),
    Node48(Indices48<Node<K, V, P>>),
    Node256(Indices256<Node<K, V, P>>),
}

impl<K, V, const P: usize> InnerIndices<K, V, P> {
    fn min_leaf_recursive(&self) -> Option<&Leaf<K, V>> {
        match self {
            Self::Node4(indices) => indices.min(),
            Self::Node16(indices) => indices.min(),
            Self::Node48(indices) => indices.min(),
            Self::Node256(indices) => indices.min(),
        }
        .and_then(|child| match child {
            Node::Leaf(leaf) => Some(leaf),
            Node::Inner(inner) => inner.indices.min_leaf_recursive(),
        })
    }

    fn max_leaf_recursive(&self) -> Option<&Leaf<K, V>> {
        match self {
            Self::Node4(indices) => indices.max(),
            Self::Node16(indices) => indices.max(),
            Self::Node48(indices) => indices.max(),
            Self::Node256(indices) => indices.max(),
        }
        .and_then(|child| match child {
            Node::Leaf(leaf) => Some(leaf),
            Node::Inner(inner) => inner.indices.max_leaf_recursive(),
        })
    }
}

/// A partial key is used to support path compression. Only a part of the prefix that matches the
/// original key is stored in the inner node.
#[derive(Debug, Clone)]
struct PartialKey<const N: usize> {
    /// The length of the prefix that matches the original key, which can be longer than the length
    /// of the data array.
    len: usize,
    /// The data array that holds the partial prefix.
    data: [u8; N],
}

impl<const N: usize> PartialKey<N> {
    /// Creates a new partial key from the given key and prefix length. We only copy at most N
    /// bytes from the key to fill the data array.
    fn new(key: &[u8], len: usize) -> Self {
        let partial_len = min(N, len);
        let mut data = [0; N];
        data[..partial_len].copy_from_slice(&key[..partial_len]);
        Self { len, data }
    }

    /// Pushes a single byte into the partial key. If the data array is full, then the byte will
    /// not be written into it. In that case, only the length will be incremented.
    fn push(&mut self, char: u8) {
        if self.len < N {
            self.data[self.len] = char;
        }
        self.len += 1;
    }

    /// Appends the data from another partial key into this one. We only copy enough bytes to fill
    /// the data array. The length will be incremented by the length of the other partial key.
    fn append(&mut self, other: &Self) {
        if self.len < N {
            let len = min(other.len, N - self.len);
            self.data[self.len..self.len + len].copy_from_slice(&other.data[..len]);
        }
        self.len += other.len;
    }

    /// Returns true if the partial key matches the given key. We only check at most N bytes.
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
