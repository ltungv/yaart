//! Implementation of Adaptive Radix Tree.

use std::{cmp::min, mem::MaybeUninit};

const MAX_PREFIX_LEN: usize = 8;

/// An adaptive radix tree. This structure contains the root node of the tree and serves as the
/// entrypoint for all tree operations.
#[derive(Debug, Default)]
pub struct Tree<K, V>(Option<Node<K, V>>);

impl<K, V> Tree<K, V>
where
    K: BytesComparable,
{
    /// Search for the value associated with the given key.
    pub fn search(&self, key: &K) -> Option<&V> {
        self.0.as_ref().and_then(|node| node.search(key))
    }

    /// Insert the given key-value pair into the tree.
    pub fn insert(&mut self, key: K, value: V) {
        if let Some(ref mut root) = self.0 {
            root.insert(key, value);
        } else {
            self.0.replace(Node::leaf(key, value));
        }
    }
}

trait Indexed<K, V> {
    fn get_header(&self) -> &NodeHeader;

    fn set_child(&mut self, key: u8, child: Node<K, V>) -> bool;

    fn get_child(&self, key: u8) -> Option<&Node<K, V>>;

    fn get_child_mut(&mut self, key: u8) -> Option<&mut Node<K, V>>;

    fn min_leaf(&self) -> Option<&Leaf<K, V>>;

    fn max_leaf(&self) -> Option<&Leaf<K, V>>;
}

#[derive(Debug, Clone)]
enum Node<K, V> {
    Leaf(Box<Leaf<K, V>>),
    Node4(Box<Node4<K, V>>),
    Node16(Box<Node16<K, V>>),
    Node48(Box<Node48<K, V>>),
    Node256(Box<Node256<K, V>>),
}

impl<K, V> Node<K, V> {
    fn leaf(key: K, value: V) -> Self {
        Self::Leaf(Box::new(Leaf { key, value }))
    }

    fn min_leaf(&self) -> Option<&Leaf<K, V>> {
        match self {
            Self::Leaf(leaf) => Some(leaf),
            Self::Node4(node) => node.min_leaf(),
            Self::Node16(node) => node.min_leaf(),
            Self::Node48(node) => node.min_leaf(),
            Self::Node256(node) => node.min_leaf(),
        }
    }

    fn max_leaf(&self) -> Option<&Leaf<K, V>> {
        match self {
            Self::Leaf(leaf) => Some(leaf),
            Self::Node4(node) => node.max_leaf(),
            Self::Node16(node) => node.max_leaf(),
            Self::Node48(node) => node.max_leaf(),
            Self::Node256(node) => node.max_leaf(),
        }
    }
}

impl<K, V> Node<K, V>
where
    K: BytesComparable,
{
    fn search(&self, key: &K) -> Option<&V> {
        let key_bytes = key.bytes();
        self.search_inner(key_bytes.as_ref(), 0)
    }

    fn search_inner(&self, key: &[u8], depth: usize) -> Option<&V> {
        match self {
            Self::Leaf(node) => {
                if !node.match_key(key) {
                    return None;
                }
                Some(&node.value)
            }
            Self::Node4(node) => Self::search_indexed(node.as_ref(), key, depth),
            Self::Node16(node) => Self::search_indexed(node.as_ref(), key, depth),
            Self::Node48(node) => Self::search_indexed(node.as_ref(), key, depth),
            Self::Node256(node) => Self::search_indexed(node.as_ref(), key, depth),
        }
    }

    fn search_indexed<'a, N>(node: &'a N, key: &[u8], depth: usize) -> Option<&'a V>
    where
        K: 'a,
        N: Indexed<K, V>,
    {
        let header = node.get_header();
        if !header.match_partial(&key[depth..]) {
            return None;
        }
        let next_depth = depth + header.partial_len;
        node.get_child(key[next_depth])
            .and_then(|child| child.search_inner(key, next_depth + 1))
    }

    fn insert(&mut self, key: K, value: V) {
        self.insert_inner(key, value, 0);
    }

    fn insert_inner(&mut self, key: K, value: V, depth: usize) {
        match self {
            Self::Leaf(old_leaf) => {
                // If the key already exists, then update the value.
                if old_leaf.match_key(key.bytes().as_ref()) {
                    old_leaf.value = value;
                    return;
                }
                // Create a new Node4.
                let (node4, new_index, old_index) = {
                    let new_key_bytes = key.bytes();
                    let old_key_bytes = old_leaf.key.bytes();
                    let new_key_bytes_ref = &new_key_bytes.as_ref()[depth..];
                    let old_key_bytes_ref = &old_key_bytes.as_ref()[depth..];
                    let prefix_len = longest_common_prefix(new_key_bytes_ref, old_key_bytes_ref);
                    let header = NodeHeader::new(prefix_len, new_key_bytes_ref);
                    let node4 = Node4::new(header);
                    (
                        node4,
                        new_key_bytes_ref[prefix_len],
                        old_key_bytes_ref[prefix_len],
                    )
                };
                // Replace the old leaf with the new Node48, and insert the leaves into it.
                let new_leaf_node = Self::leaf(key, value);
                let old_leaf_node = std::mem::replace(self, Self::Node4(Box::new(node4)));
                if let Self::Node4(node4) = self {
                    node4.set_child(new_index, new_leaf_node);
                    node4.set_child(old_index, old_leaf_node);
                } else {
                    panic!("unexpected node type")
                };
            }
            Self::Node4(_) => unimplemented!("to be added"),
            Self::Node16(_) => unimplemented!("to be added"),
            Self::Node48(_) => unimplemented!("to be added"),
            Self::Node256(_) => unimplemented!("to be added"),
        };
    }

    fn insert_indexed<N>(node: &mut N, key: K, value: V, depth: usize)
    where
        N: Indexed<K, V>,
    {
        let header = node.get_header();
        if header.partial_len > 0 {
            let prefix_diff = {
                let key_bytes = key.bytes();
                Self::first_prefix_mismatch(node, key_bytes.as_ref(), depth)
            };
            if prefix_diff >= header.partial_len {
                Self::insert_child(node, key, value, depth + header.partial_len);
            } else {
                todo!()
            }
        } else {
            Self::insert_child(node, key, value, depth);
        }
    }

    fn insert_child<N>(node: &mut N, key: K, value: V, depth: usize)
    where
        N: Indexed<K, V>,
    {
        let leaf_idx = {
            let key_bytes = key.bytes();
            key_bytes.as_ref()[depth]
        };
        if let Some(child) = node.get_child_mut(leaf_idx) {
            child.insert_inner(key, value, depth + 1);
        } else {
            let new_leaf = Self::leaf(key, value);
            node.set_child(leaf_idx, new_leaf);
        }
    }

    fn first_prefix_mismatch<'a, N>(node: &'a N, key: &[u8], depth: usize) -> usize
    where
        K: 'a,
        N: Indexed<K, V>,
    {
        let header = node.get_header();
        let len = min(MAX_PREFIX_LEN, header.partial_len);
        // Check for mismatch between the partial key and the key.
        let mut idx = 0;
        for (l, r) in header.partial[..len].iter().zip(key[depth..].iter()) {
            if l != r {
                return idx;
            }
            idx += 1;
        }
        // Common prefix is longer than the partial key, so check for mismatch between the inserted
        // key and the minimum leaf key.
        if header.partial_len > MAX_PREFIX_LEN {
            let next_depth = depth + idx;
            let leaf = node.min_leaf().expect("unable to get the minimum leaf");
            let leaf_key_bytes = leaf.key.bytes();
            for (l, r) in leaf_key_bytes.as_ref()[next_depth..]
                .iter()
                .zip(key[next_depth..].iter())
            {
                if l != r {
                    return idx;
                }
                idx += 1;
            }
        }
        idx
    }
}

#[derive(Debug, Clone)]
struct Leaf<K, V> {
    pub(crate) key: K,
    pub(crate) value: V,
}

impl<K, V> Leaf<K, V>
where
    K: BytesComparable,
{
    fn match_key(&self, key: &[u8]) -> bool {
        self.key.bytes().as_ref() == key
    }
}

#[derive(Debug, Default, Clone)]
struct NodeHeader {
    partial_len: usize,
    partial: [u8; MAX_PREFIX_LEN],
}

impl NodeHeader {
    fn new(partial_len: usize, key: &[u8]) -> Self {
        let len = min(partial_len, MAX_PREFIX_LEN);
        let mut partial = [0; MAX_PREFIX_LEN];
        partial[..len].copy_from_slice(&key[..len]);
        Self {
            partial_len,
            partial,
        }
    }

    fn match_partial(&self, key: &[u8]) -> bool {
        let len = min(MAX_PREFIX_LEN, self.partial_len);
        longest_common_prefix(&self.partial[..len], key) == len
    }
}

#[derive(Debug)]
struct Node4<K, V> {
    header: NodeHeader,
    len: u8,
    keys: [u8; 4],
    children: [MaybeUninit<Node<K, V>>; 4],
}

impl<K, V> Clone for Node4<K, V>
where
    K: Clone,
    V: Clone,
{
    fn clone(&self) -> Self {
        let mut children = make_uninitialized_array();
        for (idx, child) in self.children[..self.len as usize].iter().enumerate() {
            // SAFETY: Children whose index is below `self.len` must have been
            // initialized.
            let child_ref = unsafe { child.assume_init_ref() };
            children[idx] = MaybeUninit::new(child_ref.clone());
        }
        Self {
            header: self.header.clone(),
            len: self.len,
            keys: self.keys,
            children,
        }
    }
}

impl<K, V> Indexed<K, V> for Node4<K, V> {
    fn get_header(&self) -> &NodeHeader {
        &self.header
    }

    fn get_child(&self, key: u8) -> Option<&Node<K, V>> {
        self.keys[..self.len as usize]
            .iter()
            .position(|&k| k == key)
            .map(|idx| {
                // SAFETY: If we found a matching key, then the corresponding child must have been
                // initialized.
                unsafe { self.children[idx].assume_init_ref() }
            })
    }

    fn get_child_mut(&mut self, key: u8) -> Option<&mut Node<K, V>> {
        self.keys[..self.len as usize]
            .iter_mut()
            .position(|&mut k| k == key)
            .map(|idx| {
                // SAFETY: If we found a matching key, then the corresponding child must have been
                // initialized.
                unsafe { self.children[idx].assume_init_mut() }
            })
    }

    fn set_child(&mut self, key: u8, child: Node<K, V>) -> bool {
        if self.len >= 4 {
            return false;
        }
        let idx = self.keys[..self.len as usize]
            .iter()
            .position(|&k| k > key)
            .unwrap_or(self.len as usize);
        self.len += 1;
        self.keys[idx..].rotate_right(1);
        self.keys[idx] = key;
        self.children[idx..].rotate_right(1);
        self.children[idx].write(child);
        true
    }

    fn min_leaf(&self) -> Option<&Leaf<K, V>> {
        if self.len == 0 {
            return None;
        }
        // SAFETY: Children whose index is less than `len` must have been initialized.
        let child = unsafe { self.children[0].assume_init_ref() };
        child.min_leaf()
    }

    fn max_leaf(&self) -> Option<&Leaf<K, V>> {
        if self.len == 0 {
            return None;
        }
        // SAFETY: Children whose index is less than `len` must have been initialized.
        let child = unsafe { self.children[self.len as usize - 1].assume_init_ref() };
        child.min_leaf()
    }
}

impl<K, V> Node4<K, V> {
    fn new(header: NodeHeader) -> Self {
        Self {
            header,
            len: 0,
            keys: [0; 4],
            children: make_uninitialized_array(),
        }
    }
}

#[derive(Debug)]
struct Node16<K, V> {
    header: NodeHeader,
    len: u8,
    keys: [u8; 16],
    children: [MaybeUninit<Node<K, V>>; 16],
}

impl<K, V> Clone for Node16<K, V>
where
    K: Clone,
    V: Clone,
{
    fn clone(&self) -> Self {
        let mut children = make_uninitialized_array();
        for (idx, child) in self.children[..self.len as usize].iter().enumerate() {
            // SAFETY: Children whose index is below `self.len` must have been
            // initialized.
            let child_ref = unsafe { child.assume_init_ref() };
            children[idx] = MaybeUninit::new(child_ref.clone());
        }
        Self {
            header: self.header.clone(),
            len: self.len,
            keys: self.keys,
            children,
        }
    }
}

impl<K, V> Indexed<K, V> for Node16<K, V> {
    fn get_header(&self) -> &NodeHeader {
        &self.header
    }

    fn get_child(&self, key: u8) -> Option<&Node<K, V>> {
        let mut l = 0;
        let mut r = self.len;
        while l < r {
            let m = (l + r) / 2;
            match self.keys[m as usize].cmp(&key) {
                std::cmp::Ordering::Less => l = m + 1,
                std::cmp::Ordering::Greater => r = m,
                std::cmp::Ordering::Equal => {
                    // SAFETY: If we found a matching key, then the corresponding child must have
                    // been initialized.
                    let child = unsafe { self.children[m as usize].assume_init_ref() };
                    return Some(child);
                }
            }
        }
        None
    }

    fn get_child_mut(&mut self, key: u8) -> Option<&mut Node<K, V>> {
        self.keys[..self.len as usize]
            .iter_mut()
            .position(|&mut k| k == key)
            .map(|idx| {
                // SAFETY: If we found a matching key, then the corresponding child must have been
                // initialized.
                unsafe { self.children[idx].assume_init_mut() }
            })
    }

    fn set_child(&mut self, key: u8, child: Node<K, V>) -> bool {
        if self.len >= 16 {
            return false;
        }
        let mut l = 0;
        let mut r = self.len;
        while l < r {
            let m = (l + r) / 2;
            match self.keys[m as usize].cmp(&key) {
                std::cmp::Ordering::Less => l = m + 1,
                std::cmp::Ordering::Greater => r = m,
                std::cmp::Ordering::Equal => l = m,
            }
        }
        let idx = l as usize;
        self.len += 1;
        self.keys[idx..].rotate_right(1);
        self.keys[idx] = key;
        self.children[idx..].rotate_right(1);
        self.children[idx].write(child);
        true
    }

    fn min_leaf(&self) -> Option<&Leaf<K, V>> {
        if self.len == 0 {
            return None;
        }
        // SAFETY: Children whose index is less than `len` must have been initialized.
        let child = unsafe { self.children[0].assume_init_ref() };
        child.min_leaf()
    }

    fn max_leaf(&self) -> Option<&Leaf<K, V>> {
        if self.len == 0 {
            return None;
        }
        // SAFETY: Children whose index is less than `len` must have been initialized.
        let child = unsafe { self.children[self.len as usize - 1].assume_init_ref() };
        child.max_leaf()
    }
}

impl<K, V> Node16<K, V> {
    fn new(header: NodeHeader) -> Self {
        Self {
            header,
            len: 0,
            keys: [0; 16],
            children: make_uninitialized_array(),
        }
    }
}

#[derive(Debug)]
struct Node48<K, V> {
    header: NodeHeader,
    len: u8,
    indices: [Option<u8>; 256],
    children: [MaybeUninit<Node<K, V>>; 48],
}

impl<K, V> Clone for Node48<K, V>
where
    K: Clone,
    V: Clone,
{
    fn clone(&self) -> Self {
        let mut children = make_uninitialized_array();
        for (idx, child) in self.children[..self.len as usize].iter().enumerate() {
            // SAFETY: Children whose index is less than `len` must have been
            // initialized.
            let child_ref = unsafe { child.assume_init_ref() };
            children[idx] = MaybeUninit::new(child_ref.clone());
        }
        Self {
            header: self.header.clone(),
            len: self.len,
            indices: self.indices,
            children,
        }
    }
}

impl<K, V> Indexed<K, V> for Node48<K, V> {
    fn get_header(&self) -> &NodeHeader {
        &self.header
    }

    fn get_child(&self, key: u8) -> Option<&Node<K, V>> {
        self.indices[key as usize].map(|idx| {
            // SAFETY: If we found Some(index), then the corresponding child must have been
            // initialized.
            unsafe { self.children[idx as usize].assume_init_ref() }
        })
    }

    fn get_child_mut(&mut self, key: u8) -> Option<&mut Node<K, V>> {
        self.indices[key as usize].map(|idx| {
            // SAFETY: If we found Some(index), then the corresponding child must have been
            // initialized.
            unsafe { self.children[idx as usize].assume_init_mut() }
        })
    }

    fn set_child(&mut self, key: u8, child: Node<K, V>) -> bool {
        if self.len >= 48 {
            return false;
        }
        let idx = self.len;
        self.len += 1;
        self.indices[key as usize] = Some(idx);
        self.children[idx as usize].write(child);
        true
    }

    fn min_leaf(&self) -> Option<&Leaf<K, V>> {
        self.indices.iter().flatten().next().and_then(|&idx| {
            // SAFETY: If we found Some(index), then the corresponding child must have been
            // initialized.
            let child = unsafe { self.children[idx as usize].assume_init_ref() };
            child.max_leaf()
        })
    }

    fn max_leaf(&self) -> Option<&Leaf<K, V>> {
        self.indices.iter().rev().flatten().next().and_then(|&idx| {
            // SAFETY: If we found Some(index), then the corresponding child must have been
            // initialized.
            let child = unsafe { self.children[idx as usize].assume_init_ref() };
            child.max_leaf()
        })
    }
}

impl<K, V> Node48<K, V> {
    fn new(header: NodeHeader) -> Self {
        Self {
            header,
            len: 0,
            indices: [None; 256],
            children: make_uninitialized_array(),
        }
    }
}

#[derive(Debug, Clone)]
struct Node256<K, V> {
    header: NodeHeader,
    children: [Option<Node<K, V>>; 256],
}

impl<K, V> Indexed<K, V> for Node256<K, V> {
    fn get_header(&self) -> &NodeHeader {
        &self.header
    }

    fn get_child(&self, key: u8) -> Option<&Node<K, V>> {
        self.children[key as usize].as_ref()
    }

    fn get_child_mut(&mut self, key: u8) -> Option<&mut Node<K, V>> {
        self.children[key as usize].as_mut()
    }

    fn set_child(&mut self, key: u8, child: Node<K, V>) -> bool {
        self.children[key as usize] = Some(child);
        true
    }

    fn min_leaf(&self) -> Option<&Leaf<K, V>> {
        self.children
            .iter()
            .flatten()
            .next()
            .and_then(Node::min_leaf)
    }

    fn max_leaf(&self) -> Option<&Leaf<K, V>> {
        self.children
            .iter()
            .rev()
            .flatten()
            .next()
            .and_then(Node::max_leaf)
    }
}

impl<K, V> Node256<K, V> {
    const DEFAULT_CHILD: Option<Node<K, V>> = None;

    const fn new(header: NodeHeader) -> Self {
        Self {
            header,
            children: [Self::DEFAULT_CHILD; 256],
        }
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

fn make_uninitialized_array<T, const N: usize>() -> [MaybeUninit<T>; N] {
    // SAFETY: calling `assume_init` to convert an uninitialized array
    // into an array of uninitialized items is safe.
    unsafe { MaybeUninit::uninit().assume_init() }
}

#[cfg(test)]
mod tests {
    use crate::art::{Node, Node16, Node256, Node48, NodeHeader};

    use super::{Indexed, Node4};

    #[test]
    fn test_node4_set_child() {
        let mut node = Node4::<usize, usize>::new(NodeHeader::default());
        for i in 0..4 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
        }
        assert!(!node.set_child(4, Node::leaf(4, 4)));
    }

    #[test]
    fn test_node4_get_child() {
        let mut node = Node4::<usize, usize>::new(NodeHeader::default());
        for i in 0..4 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
        }
        for i in 0..4 {
            if let Node::Leaf(leaf) = node.get_child(i).unwrap() {
                assert_eq!(leaf.key, i as usize);
                assert_eq!(leaf.value, i as usize);
            } else {
                panic!("unexpected node type");
            }
        }
        assert!(node.get_child(4).is_none());
    }

    #[test]
    fn test_node4_min_max_child() {
        let mut node = Node4::<usize, usize>::new(NodeHeader::default());
        for i in 0..4 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
            let min_leaf = node.min_leaf().unwrap();
            let max_leaf = node.max_leaf().unwrap();
            assert_eq!(min_leaf.key, 0);
            assert_eq!(min_leaf.key, 0);
            assert_eq!(max_leaf.key, i as usize);
            assert_eq!(max_leaf.key, i as usize);
        }

        let mut node = Node4::<usize, usize>::new(NodeHeader::default());
        for i in (0..4).rev() {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
            let min_leaf = node.min_leaf().unwrap();
            let max_leaf = node.max_leaf().unwrap();
            assert_eq!(min_leaf.key, i as usize);
            assert_eq!(min_leaf.key, i as usize);
            assert_eq!(max_leaf.key, 3);
            assert_eq!(max_leaf.key, 3);
        }
    }

    #[test]
    fn test_node16_set_child() {
        let mut node = Node16::<usize, usize>::new(NodeHeader::default());
        for i in 0..16 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
        }
        assert!(!node.set_child(16, Node::leaf(16, 16)));
    }

    #[test]
    fn test_node16_get_child() {
        let mut node = Node16::<usize, usize>::new(NodeHeader::default());
        for i in 0..16 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
        }
        for i in 0..16 {
            if let Node::Leaf(leaf) = node.get_child(i).unwrap() {
                assert_eq!(leaf.key, i as usize);
                assert_eq!(leaf.value, i as usize);
            } else {
                panic!("unexpected node type");
            }
        }
        assert!(node.get_child(16).is_none());
    }

    #[test]
    fn test_node16_min_max_child() {
        let mut node = Node16::<usize, usize>::new(NodeHeader::default());
        for i in 0..16 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
            let min_leaf = node.min_leaf().unwrap();
            let max_leaf = node.max_leaf().unwrap();
            assert_eq!(min_leaf.key, 0);
            assert_eq!(min_leaf.key, 0);
            assert_eq!(max_leaf.key, i as usize);
            assert_eq!(max_leaf.key, i as usize);
        }

        let mut node = Node16::<usize, usize>::new(NodeHeader::default());
        for i in (0..16).rev() {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
            let min_leaf = node.min_leaf().unwrap();
            let max_leaf = node.max_leaf().unwrap();
            assert_eq!(min_leaf.key, i as usize);
            assert_eq!(min_leaf.key, i as usize);
            assert_eq!(max_leaf.key, 15);
            assert_eq!(max_leaf.key, 15);
        }
    }

    #[test]
    fn test_node48_set_child() {
        let mut node = Node48::<usize, usize>::new(NodeHeader::default());
        for i in 0..48 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
        }
        assert!(!node.set_child(48, Node::leaf(48, 48)));
    }

    #[test]
    fn test_node48_get_child() {
        let mut node = Node48::<usize, usize>::new(NodeHeader::default());
        for i in 0..48 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
        }
        for i in 0..48 {
            if let Node::Leaf(leaf) = node.get_child(i).unwrap() {
                assert_eq!(leaf.key, i as usize);
                assert_eq!(leaf.value, i as usize);
            } else {
                panic!("unexpected node type");
            }
        }
        assert!(node.get_child(48).is_none());
    }

    #[test]
    fn test_node48_min_max_child() {
        let mut node = Node48::<usize, usize>::new(NodeHeader::default());
        for i in 0..48 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
            let min_leaf = node.min_leaf().unwrap();
            let max_leaf = node.max_leaf().unwrap();
            assert_eq!(min_leaf.key, 0);
            assert_eq!(min_leaf.key, 0);
            assert_eq!(max_leaf.key, i as usize);
            assert_eq!(max_leaf.key, i as usize);
        }

        let mut node = Node48::<usize, usize>::new(NodeHeader::default());
        for i in (0..48).rev() {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
            let min_leaf = node.min_leaf().unwrap();
            let max_leaf = node.max_leaf().unwrap();
            assert_eq!(min_leaf.key, i as usize);
            assert_eq!(min_leaf.key, i as usize);
            assert_eq!(max_leaf.key, 47);
            assert_eq!(max_leaf.key, 47);
        }
    }

    #[test]
    fn test_node256_set_child() {
        let mut node = Node256::<usize, usize>::new(NodeHeader::default());
        for i in 0..=255 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
        }
        assert!(node.set_child(255, Node::leaf(256, 256)));
    }

    #[test]
    fn test_node256_get_child() {
        let mut node = Node256::<usize, usize>::new(NodeHeader::default());
        for i in 0..=255 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
        }
        for i in 0..=255 {
            if let Node::Leaf(leaf) = node.get_child(i).unwrap() {
                assert_eq!(leaf.key, i as usize);
                assert_eq!(leaf.value, i as usize);
            } else {
                panic!("unexpected node type");
            }
        }
    }

    #[test]
    fn test_node256_min_max_child() {
        let mut node = Node256::<usize, usize>::new(NodeHeader::default());
        for i in 0..=255 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
            let min_leaf = node.min_leaf().unwrap();
            let max_leaf = node.max_leaf().unwrap();
            assert_eq!(min_leaf.key, 0);
            assert_eq!(min_leaf.key, 0);
            assert_eq!(max_leaf.key, i as usize);
            assert_eq!(max_leaf.key, i as usize);
        }

        let mut node = Node256::<usize, usize>::new(NodeHeader::default());
        for i in (0..=255).rev() {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
            let min_leaf = node.min_leaf().unwrap();
            let max_leaf = node.max_leaf().unwrap();
            assert_eq!(min_leaf.key, i as usize);
            assert_eq!(min_leaf.key, i as usize);
            assert_eq!(max_leaf.key, 255);
            assert_eq!(max_leaf.key, 255);
        }
    }

    #[test]
    fn test_leaf_node_insert() {
        let mut node = Node::leaf(0, 0);
        assert_eq!(node.search(&0), Some(&0));

        node.insert(0, 1);
        node.insert(69, 420);
        assert_eq!(node.search(&0), Some(&1));
        assert_eq!(node.search(&69), Some(&420));
        assert_eq!(node.search(&420), None);
    }
}
