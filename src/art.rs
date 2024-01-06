//! # Adaptive Radix Tree.

use std::cmp::min;

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
            root.debug_print(f, 0, 0)
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
    pub fn search(&self, key: &K) -> Option<&V> {
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
}

#[derive(Debug)]
enum Node<K, V, const P: usize> {
    Leaf(Box<Leaf<K, V>>),
    Internal(Box<Internal<K, V, P>>),
}

impl<K, V, const P: usize> Node<K, V, P> {
    fn new_leaf(key: K, value: V) -> Self {
        Self::Leaf(Box::new(Leaf { key, value }))
    }

    fn new_internal(partial: PartialKey<P>) -> Self {
        Self::Internal(Box::new(Internal::new(partial)))
    }

    fn add_child(&mut self, key: u8, child: Self) {
        match self {
            Self::Internal(node) => node.indices.add_child(key, child),
            Self::Leaf(_) => panic!("[bug] can't add child to leaf"),
        }
    }
}

impl<K, V, const P: usize> Node<K, V, P>
where
    K: BytesComparable,
{
    fn search(&self, key: &K) -> Option<&V> {
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
                let new_key_bytes = key.bytes();
                if leaf.match_key(new_key_bytes.as_ref()) {
                    // Inserting an existing key.
                    leaf.value = value;
                    return;
                }
                // Determines the partial key for the new node and the keys for the two children.
                let old_key_bytes = leaf.key.bytes();
                let prefix_len =
                    longest_common_prefix(new_key_bytes.as_ref(), old_key_bytes.as_ref(), depth);
                let new_depth = depth + prefix_len;
                let partial = PartialKey::new(new_key_bytes.as_ref(), prefix_len, depth);
                let k_new = new_key_bytes.as_ref()[new_depth];
                let k_old = old_key_bytes.as_ref()[new_depth];
                // Drop these so we can move the keys.
                drop(new_key_bytes);
                drop(old_key_bytes);
                // Replace the current node, then add the old leaf and new leaf as its children.
                let new_leaf = Self::new_leaf(key, value);
                let old_leaf = std::mem::replace(self, Self::new_internal(partial));
                self.add_child(k_new, new_leaf);
                self.add_child(k_old, old_leaf);
            }
            Self::Internal(_node) => todo!(),
        }
    }
}

impl<K, V, const P: usize> Node<K, V, P>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    pub fn debug_print(
        &self,
        formatter: &mut std::fmt::Formatter<'_>,
        key: u8,
        level: usize,
    ) -> std::fmt::Result {
        fn print_indentation(
            formatter: &mut std::fmt::Formatter<'_>,
            level: usize,
        ) -> std::fmt::Result {
            for _ in 0..level {
                write!(formatter, "  ")?;
            }
            Ok(())
        }

        print_indentation(formatter, level)?;
        match self {
            Self::Leaf(leaf) => {
                writeln!(
                    formatter,
                    "[{:03}] leaf: {:?} -> {:?}",
                    key, leaf.key, leaf.value
                )?;
            }
            Self::Internal(node) => match &node.indices {
                InternalIndices::Node4(indices) => {
                    writeln!(formatter, "[{:03}] node4 {:?}", key, node.partial)?;
                    for (key, child) in indices {
                        child.debug_print(formatter, key, level + 1)?;
                    }
                }
                InternalIndices::Node16(indices) => {
                    writeln!(formatter, "[{:03}] node16 {:?}", key, node.partial)?;
                    for (key, child) in indices {
                        child.debug_print(formatter, key, level + 1)?;
                    }
                }
                InternalIndices::Node48(indices) => {
                    writeln!(formatter, "[{:03}] node48 {:?}", key, node.partial)?;
                    for (key, child) in indices {
                        child.debug_print(formatter, key, level + 1)?;
                    }
                }
                InternalIndices::Node256(indices) => {
                    writeln!(formatter, "[{:03}] node256 {:?}", key, node.partial)?;
                    for (key, child) in indices {
                        child.debug_print(formatter, key, level + 1)?;
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
struct Internal<K, V, const P: usize> {
    partial: PartialKey<P>,
    indices: InternalIndices<K, V, P>,
}

impl<K, V, const P: usize> Internal<K, V, P> {
    fn new(partial: PartialKey<P>) -> Self {
        Self {
            partial,
            indices: InternalIndices::Node4(indices::Sorted::default()),
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
        let child = match &self.indices {
            InternalIndices::Node4(node) => node.child_ref(key[next_depth]),
            InternalIndices::Node16(node) => node.child_ref(key[next_depth]),
            InternalIndices::Node48(node) => node.child_ref(key[next_depth]),
            InternalIndices::Node256(node) => node.child_ref(key[next_depth]),
        };
        child.and_then(|child| child.search_recursive(key, next_depth + 1))
    }
}

#[derive(Debug)]
enum InternalIndices<K, V, const P: usize> {
    Node4(indices::Sorted<Node<K, V, P>, 4>),
    Node16(indices::Sorted<Node<K, V, P>, 16>),
    Node48(indices::Indirect<Node<K, V, P>, 48>),
    Node256(indices::Direct<Node<K, V, P>>),
}

impl<K, V, const P: usize> InternalIndices<K, V, P> {
    fn add_child(&mut self, key: u8, child: Node<K, V, P>) {
        match self {
            Self::Node4(node) => node.add_child(key, child),
            Self::Node16(node) => node.add_child(key, child),
            Self::Node48(node) => node.add_child(key, child),
            Self::Node256(node) => node.add_child(key, child),
        }
    }
}

#[derive(Debug, Clone)]
struct PartialKey<const N: usize> {
    len: usize,
    data: [u8; N],
}

impl<const N: usize> PartialKey<N> {
    fn new(key: &[u8], len: usize, depth: usize) -> Self {
        let partial_len = min(N, len);
        let mut data = [0; N];
        data[..partial_len].copy_from_slice(&key[depth..depth + partial_len]);
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

impl BytesComparable for Vec<u8> {
    type Target<'a> = &'a [u8];

    fn bytes(&self) -> Self::Target<'_> {
        self.as_slice()
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
        .position(|(x, y)| x != y)
        .unwrap_or(0)
}

#[cfg(test)]
mod tests {
    use crate::Tree;

    #[test]
    fn test_insert_tree_tiny() {
        let mut tree = Tree::<u64, u64>::default();
        tree.insert(0, 0);
        tree.insert(1, 1);
        let v0 = tree.search(&0);
        let v1 = tree.search(&1);
        assert_eq!(v0, Some(0).as_ref());
        assert_eq!(v1, Some(1).as_ref());
    }
}
