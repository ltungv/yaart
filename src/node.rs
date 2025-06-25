use crate::{
    compressed_path::CompressedPath,
    index::{Index, Index16, Index256, Index4, Index48},
    BytesComparable, SearchKey,
};

/// A node in the ART, which can be either an inner node or a leaf node. Leaf nodes hold data of
/// key-value pairs, and inner nodes holds index to its children.
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
    fn new_inner(path: CompressedPath<P>) -> Self {
        Self::Inner(Inner::new(path))
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
    ///   and depends on the length of prefixes along the path.
    pub fn search(&self, key: SearchKey<&[u8]>, depth: usize) -> Option<&Leaf<K, V>> {
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
    ///   and depends on the length of prefixes along the path.
    pub fn insert(&mut self, key: K, value: V, depth: usize) {
        match self {
            Self::Leaf(leaf) => {
                // Here we create a scope to avoid borrowing `key` for too long in order to move it into the new leaf.
                let (path, k_new, k_old) = {
                    let new_key_bytes = key.key();
                    // If the leaf's key matches the new key, then update it's value and return early.
                    if leaf.match_key(new_key_bytes.into_ref()) {
                        leaf.value = value;
                        return;
                    }
                    // Calculates the common prefix length between the new key and the leaf's key.
                    let old_key_bytes = leaf.key.key();
                    let prefix_len = new_key_bytes
                        .into_ref()
                        .common_prefix_len(&old_key_bytes, depth);
                    // Creates a new compressed path from the common prefix. Then gets the new and old byte keys of where
                    // the leaves are placed within the inner node.
                    let new_depth = depth + prefix_len;
                    (
                        CompressedPath::new(new_key_bytes.from(depth).as_ref(), prefix_len),
                        new_key_bytes.get(new_depth),
                        old_key_bytes.get(new_depth),
                    )
                };
                // Replace the current node, then add the old leaf and new leaf as its children.
                let new_leaf = Self::new_leaf(key, value);
                let old_leaf = std::mem::replace(self, Self::new_inner(path));
                self.add_child(k_new, new_leaf);
                self.add_child(k_old, old_leaf);
            }
            Self::Inner(inner) => {
                // Inner node has no prefix, insert recursively into it without any checks or modifications.
                if inner.path.prefix_len() == 0 {
                    return inner.insert_recursive(key, value, depth);
                }
                // Find the index at which the new key differs from the inner node's compressed
                // path.
                let (prefix_diff, new_byte_key) = {
                    let key_bytes = key.key();
                    let prefix_diff = inner.mismatch(key_bytes.into_ref(), depth);
                    let byte_key = key_bytes.get(depth + prefix_diff);
                    (prefix_diff, byte_key)
                };
                // The index at which the new key differs is not covered by the current compressed
                // path, so we insert recursively.
                if prefix_diff >= inner.path.prefix_len() {
                    return inner.insert_recursive(key, value, depth + inner.path.prefix_len());
                }
                // At this point, we found a difference between the new key and the inner node's
                // compressed path.
                let shift = prefix_diff + 1;
                let path = CompressedPath::new(inner.path.as_ref(), prefix_diff);
                if inner.path.prefix_len() <= P {
                    // The mismatched byte is contained within the compressed path data. We modify
                    // the inner node compressed path by skipping the common prefix plus the first
                    // byte where the keys differ. A new inner node is created, and we add the old
                    // inner node as its child.
                    let byte_key = inner.path[prefix_diff];
                    inner.path.shift(shift);
                    let old_node = std::mem::replace(self, Self::new_inner(path));
                    self.add_child(byte_key, old_node);
                } else {
                    let Some(leaf) = inner.index.min_leaf_recursive() else {
                        unreachable!(
                            "a leaf must exist in the tree if the prefix is longer than the compressed path"
                        )
                    };
                    // The mismatched byte is contained outside of the compressed path data. We
                    // modify the inner node by filling its compressed path data with part of the
                    // common prefix copied from the minimum leaf's key. A new inner node is
                    // created, and we add the old inner node as its child.
                    let byte_key = {
                        let leaf_key_bytes = leaf.key.key();
                        let offset = depth + shift;
                        inner.path.shift_with(shift, leaf_key_bytes.from(offset));
                        leaf_key_bytes.get(depth + prefix_diff)
                    };
                    let old_node = std::mem::replace(self, Self::new_inner(path));
                    self.add_child(byte_key, old_node);
                }
                self.add_child(new_byte_key, Self::new_leaf(key, value));
            }
        }
    }

    pub fn delete(&mut self, key: SearchKey<&[u8]>, depth: usize) -> Option<Leaf<K, V>> {
        let Self::Inner(inner) = self else {
            unreachable!("can not delete child on a leaf node");
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
            Self::Inner(inner) => inner.index.min_leaf_recursive(),
        }
    }

    pub fn max_leaf(&self) -> Option<&Leaf<K, V>> {
        match self {
            Self::Leaf(leaf) => Some(leaf),
            Self::Inner(inner) => inner.index.max_leaf_recursive(),
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
        Node::Inner(inner) => match &inner.index {
            InnerIndex::Node4(index) => {
                writeln!(
                    f,
                    "[{:03}] node4 (len: {}) {:?}",
                    key,
                    index.len(),
                    inner.path
                )?;
                for (key, child) in index.as_ref() {
                    debug_print(f, child, key, level + 1)?;
                }
            }
            InnerIndex::Node16(index) => {
                writeln!(
                    f,
                    "[{:03}] node16 (len: {}) {:?}",
                    key,
                    index.len(),
                    inner.path
                )?;
                for (key, child) in index.as_ref() {
                    debug_print(f, child, key, level + 1)?;
                }
            }
            InnerIndex::Node48(index) => {
                writeln!(
                    f,
                    "[{:03}] node48 (len: {}) {:?}",
                    key,
                    index.len(),
                    inner.path
                )?;
                for (key, child) in index.as_ref() {
                    debug_print(f, child, key, level + 1)?;
                }
            }
            InnerIndex::Node256(index) => {
                writeln!(
                    f,
                    "[{:03}] node256 (len: {}) {:?}",
                    key,
                    index.len(),
                    inner.path
                )?;
                for (key, child) in index.as_ref() {
                    debug_print(f, child, key, level + 1)?;
                }
            }
        },
    }
    Ok(())
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
    pub fn match_key(&self, key: SearchKey<&[u8]>) -> bool {
        self.key.key().into_ref() == key
    }
}

#[derive(Debug)]
pub struct Inner<K, V, const P: usize> {
    path: CompressedPath<P>,
    index: InnerIndex<K, V, P>,
}

impl<K, V, const P: usize> Inner<K, V, P> {
    fn new(path: CompressedPath<P>) -> Self {
        Self {
            path,
            index: InnerIndex::Node4(Box::default()),
        }
    }
}

impl<K, V, const P: usize> Inner<K, V, P>
where
    K: BytesComparable,
{
    fn search_recursive(&self, key: SearchKey<&[u8]>, depth: usize) -> Option<&Leaf<K, V>> {
        if !self.path.check(key, depth) {
            return None;
        }
        let next_depth = depth + self.path.prefix_len();
        let byte_key = key.get(next_depth);
        self.child_ref(byte_key)
            .and_then(|child| child.search(key, next_depth + 1))
    }

    fn insert_recursive(&mut self, key: K, value: V, depth: usize) {
        let byte_key = key.key().get(depth);
        if let Some(child) = self.child_mut(byte_key) {
            // Found a child so we recursively insert into it.
            child.insert(key, value, depth + 1);
        } else {
            // No child found so we insert a new leaf into the current node.
            let leaf = Node::new_leaf(key, value);
            self.add_child(byte_key, leaf);
        }
    }

    fn delete_recursive(&mut self, key: SearchKey<&[u8]>, depth: usize) -> Option<Leaf<K, V>> {
        // The key doesn't match the prefix compressed path.
        if !self.path.check(key, depth) {
            return None;
        }
        // Find the child node corresponding to the key.
        let depth = depth + self.path.prefix_len();
        let child_key = key.get(depth);
        let child = self.child_mut(child_key)?;
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
        match &mut self.index {
            InnerIndex::Node4(index) => index.add_child(key, child),
            InnerIndex::Node16(index) => index.add_child(key, child),
            InnerIndex::Node48(index) => index.add_child(key, child),
            InnerIndex::Node256(index) => index.add_child(key, child),
        }
    }

    fn del_child(&mut self, key: u8) -> Option<Node<K, V, P>> {
        match &mut self.index {
            InnerIndex::Node4(index) => index.del_child(key),
            InnerIndex::Node16(index) => index.del_child(key),
            InnerIndex::Node48(index) => index.del_child(key),
            InnerIndex::Node256(index) => index.del_child(key),
        }
    }

    fn child_ref(&self, key: u8) -> Option<&Node<K, V, P>> {
        match &self.index {
            InnerIndex::Node4(index) => index.child_ref(key),
            InnerIndex::Node16(index) => index.child_ref(key),
            InnerIndex::Node48(index) => index.child_ref(key),
            InnerIndex::Node256(index) => index.child_ref(key),
        }
    }

    fn child_mut(&mut self, key: u8) -> Option<&mut Node<K, V, P>> {
        match &mut self.index {
            InnerIndex::Node4(index) => index.child_mut(key),
            InnerIndex::Node16(index) => index.child_mut(key),
            InnerIndex::Node48(index) => index.child_mut(key),
            InnerIndex::Node256(index) => index.child_mut(key),
        }
    }

    fn grow(&mut self) {
        match &mut self.index {
            InnerIndex::Node4(index) => {
                if index.len() == 4 {
                    self.index = InnerIndex::Node16(Box::new(Index16::from(index.as_mut())));
                }
            }
            InnerIndex::Node16(index) => {
                if index.len() == 16 {
                    self.index = InnerIndex::Node48(Box::new(Index48::from(index.as_mut())));
                }
            }
            InnerIndex::Node48(index) => {
                if index.len() == 48 {
                    self.index = InnerIndex::Node256(Box::new(Index256::from(index.as_mut())));
                }
            }
            InnerIndex::Node256(_) => {}
        }
    }

    fn shrink(&mut self) -> Option<Node<K, V, P>> {
        match &mut self.index {
            InnerIndex::Node4(index) => {
                if index.len() <= 1 {
                    let (sub_child_key, mut sub_child) = index.free();
                    if let Node::Inner(sub_child) = &mut sub_child {
                        self.path.push(sub_child_key);
                        self.path.append(&sub_child.path);
                        std::mem::swap(&mut self.path, &mut sub_child.path);
                    }
                    return Some(sub_child);
                }
            }
            InnerIndex::Node16(index) => {
                if index.len() <= 3 {
                    self.index = InnerIndex::Node4(Box::new(Index4::from(index.as_mut())));
                }
            }
            InnerIndex::Node48(index) => {
                if index.len() <= 12 {
                    self.index = InnerIndex::Node16(Box::new(Index16::from(index.as_mut())));
                }
            }
            InnerIndex::Node256(index) => {
                if index.len() <= 37 {
                    self.index = InnerIndex::Node48(Box::new(Index48::from(index.as_mut())));
                }
            }
        }
        None
    }

    fn mismatch(&self, key: SearchKey<&[u8]>, depth: usize) -> usize {
        let partial_len = self.path.partial_len();
        if let Some(idx) = self.path.mismatch(key.from(depth)) {
            return idx;
        }
        let mut idx = partial_len.min(key.len() - depth);
        if self.path.prefix_len() > P {
            // Prefix is longer than what we've checked, find a leaf. The minimum leaf is
            // guaranteed to contains the longest common prefix of the current compressed path.
            let Some(leaf) = self.index.min_leaf_recursive() else {
                unreachable!(
                    "a leaf must exist in the tree if the prefix is longer than the compressed path"
                )
            };
            idx += leaf.key.key().common_prefix_len(&key, depth + idx);
        }
        idx
    }
}

#[derive(Debug)]
enum InnerIndex<K, V, const P: usize> {
    Node4(Box<Index4<Node<K, V, P>>>),
    Node16(Box<Index16<Node<K, V, P>>>),
    Node48(Box<Index48<Node<K, V, P>>>),
    Node256(Box<Index256<Node<K, V, P>>>),
}

impl<K, V, const P: usize> InnerIndex<K, V, P> {
    fn min_leaf_recursive(&self) -> Option<&Leaf<K, V>> {
        match self {
            Self::Node4(index) => index.min(),
            Self::Node16(index) => index.min(),
            Self::Node48(index) => index.min(),
            Self::Node256(index) => index.min(),
        }
        .and_then(|child| match child {
            Node::Leaf(leaf) => Some(leaf),
            Node::Inner(inner) => inner.index.min_leaf_recursive(),
        })
    }

    fn max_leaf_recursive(&self) -> Option<&Leaf<K, V>> {
        match self {
            Self::Node4(index) => index.max(),
            Self::Node16(index) => index.max(),
            Self::Node48(index) => index.max(),
            Self::Node256(index) => index.max(),
        }
        .and_then(|child| match child {
            Node::Leaf(leaf) => Some(leaf),
            Node::Inner(inner) => inner.index.max_leaf_recursive(),
        })
    }
}
