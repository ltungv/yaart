//! # Adaptive Radix Tree.

use std::cmp::min;

use crate::indices::{self, Indices};

/// An adaptive radix tree. This structure contains the root node of the tree and serves as the
/// entrypoint for all tree operations.
#[derive(Debug, Default)]
pub struct Tree<K, V> {
    root: Option<Node<K, V, 8>>,
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
        if let Some(ref mut _root) = self.root {
            todo!()
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

#[derive(Debug)]
enum InternalIndices<K, V, const P: usize> {
    Node4(indices::Sorted<Node<K, V, P>, 4>),
    Node16(indices::Sorted<Node<K, V, P>, 16>),
    Node48(indices::Indirect<Node<K, V, P>, 48>),
    Node256(indices::Direct<Node<K, V, P>>),
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

#[derive(Debug, Clone)]
struct PartialKey<const N: usize> {
    len: usize,
    data: [u8; N],
}

impl<const N: usize> PartialKey<N> {
    fn match_key(&self, key: &[u8], depth: usize) -> bool {
        let len = min(N, self.len);
        longest_common_prefix(&self.data[..len], &key[depth..]) == len
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
fn longest_common_prefix<T>(lhs: &[T], rhs: &[T]) -> usize
where
    T: PartialEq,
{
    lhs.iter()
        .zip(rhs.iter())
        .take_while(|(x, y)| x.eq(y))
        .count()
}

#[cfg(test)]
mod tests {}
