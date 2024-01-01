use std::{cmp::min, mem::MaybeUninit};

const MAX_PREFIX_LEN: usize = 8;

struct Tree<K, V>(Option<Node<K, V>>);

impl<K, V> Tree<K, V>
where
    K: Comparable,
{
    fn search(&self, key: &K) -> Option<&V> {
        self.0.as_ref().and_then(|node| node.search(key))
    }

    fn insert(&mut self, key: K, value: V) {
        match &mut self.0 {
            Some(ref mut root) => {
                root.insert(key, value);
            }
            None => {
                self.0.replace(Node::leaf(key, value));
            }
        }
    }
}

trait Indexed<K, V> {
    fn header(&self) -> &NodeHeader;
    fn get_child(&self, key: u8) -> Option<&Node<K, V>>;
    fn set_child(&mut self, key: u8, child: Node<K, V>) -> bool;
}

#[derive(Debug)]
enum Node<K, V> {
    Leaf(Box<Leaf<K, V>>),
    Node4(Box<Node4<K, V>>),
    Node16(Box<Node16<K, V>>),
    Node48(Box<Node48<K, V>>),
    Node256(Box<Node256<K, V>>),
}

impl<K, V> Node<K, V> {
    fn leaf(key: K, value: V) -> Node<K, V> {
        Node::Leaf(Box::new(Leaf { key, value }))
    }
}

impl<K, V> Node<K, V>
where
    K: Comparable,
{
    fn search(&self, key: &K) -> Option<&V> {
        let key_bytes = key.bytes();
        self.search_inner(key_bytes.as_ref(), 0)
    }

    fn search_inner(&self, key: &[u8], depth: usize) -> Option<&V> {
        match self {
            Node::Leaf(node) => {
                if node.match_key(key) {
                    Some(&node.value)
                } else {
                    None
                }
            }
            Node::Node4(node) => Self::search_child(node.as_ref(), key, depth),
            Node::Node16(node) => Self::search_child(node.as_ref(), key, depth),
            Node::Node48(node) => Self::search_child(node.as_ref(), key, depth),
            Node::Node256(node) => Self::search_child(node.as_ref(), key, depth),
        }
    }

    fn search_child<'a, N>(node: &'a N, key: &[u8], depth: usize) -> Option<&'a V>
    where
        K: 'a,
        N: Indexed<K, V>,
    {
        let header = node.header();
        if !header.match_partial(&key[depth..]) {
            return None;
        }
        let new_depth = depth + header.partial_len as usize;
        node.get_child(key[new_depth])
            .and_then(|child| child.search_inner(key, new_depth + 1))
    }

    fn insert(&mut self, key: K, value: V) {
        self.insert_inner(key, value, 0)
    }

    fn insert_inner(&mut self, key: K, value: V, depth: usize) {
        match self {
            Node::Leaf(old_leaf) => {
                if old_leaf.match_key(key.bytes().as_ref()) {
                    old_leaf.value = value;
                } else {
                    let new_key_bytes = key.bytes();
                    let old_key_bytes = old_leaf.key.bytes();

                    let prefix_len = longest_common_prefix(
                        &new_key_bytes.as_ref()[depth..],
                        &old_key_bytes.as_ref()[depth..],
                    );

                    let header = NodeHeader::new(prefix_len as u8, new_key_bytes.as_ref());
                    let node4 = Node4::new(header);

                    let new_index = new_key_bytes.as_ref()[depth + prefix_len];
                    let old_index = old_key_bytes.as_ref()[depth + prefix_len];

                    drop(new_key_bytes);
                    drop(old_key_bytes);

                    let new_leaf_node = Node::leaf(key, value);
                    let old_leaf_node = std::mem::replace(self, Node::Node4(Box::new(node4)));
                    if let Node::Node4(node4) = self {
                        node4.set_child(new_index, new_leaf_node);
                        node4.set_child(old_index, old_leaf_node);
                    } else {
                        panic!("unexpected node type")
                    }
                }
            }
            Node::Node4(_) => unimplemented!("to be added"),
            Node::Node16(_) => unimplemented!("to be added"),
            Node::Node48(_) => unimplemented!("to be added"),
            Node::Node256(_) => unimplemented!("to be added"),
        };
    }
}

#[derive(Debug)]
struct Leaf<K, V> {
    pub(crate) key: K,
    pub(crate) value: V,
}

impl<K, V> Leaf<K, V>
where
    K: Comparable,
{
    fn match_key(&self, key: &[u8]) -> bool {
        self.key.bytes().as_ref() == key
    }
}

#[derive(Debug, Default)]
struct NodeHeader {
    partial_len: u8,
    partial: [u8; MAX_PREFIX_LEN],
}

impl NodeHeader {
    fn new(partial_len: u8, key: &[u8]) -> Self {
        let len = min(partial_len as usize, MAX_PREFIX_LEN);
        let mut partial = [0; MAX_PREFIX_LEN];
        partial[..len].copy_from_slice(&key[..len]);
        Self {
            partial_len,
            partial,
        }
    }
    fn match_partial(&self, key: &[u8]) -> bool {
        let len = min(MAX_PREFIX_LEN, self.partial_len as usize);
        longest_common_prefix(&self.partial[..len], key) == len
    }
}

#[derive(Debug)]
struct Node4<K, V> {
    header: NodeHeader,
    children_count: u8,
    keys: [u8; 4],
    children: [MaybeUninit<Node<K, V>>; 4],
}

impl<K, V> Indexed<K, V> for Node4<K, V> {
    fn header(&self) -> &NodeHeader {
        &self.header
    }

    fn get_child(&self, key: u8) -> Option<&Node<K, V>> {
        self.keys[..self.children_count as usize]
            .iter()
            .position(|&k| k == key)
            .map(|idx| {
                // SAFETY: If we found a matching key, then the corresponding
                // child must have been initialized.
                unsafe { self.children[idx].assume_init_ref() }
            })
    }

    fn set_child(&mut self, key: u8, child: Node<K, V>) -> bool {
        if self.children_count >= 4 {
            return false;
        }
        let idx = self.children_count as usize;
        self.children_count += 1;
        self.keys[idx] = key;
        self.children[idx].write(child);
        true
    }
}

impl<K, V> Node4<K, V> {
    fn new(header: NodeHeader) -> Self {
        Self {
            header,
            children_count: 0,
            keys: [0; 4],
            // SAFETY: calling `assume_init` to convert an uninitialized array
            // into an array of uninitialized items is safe.
            children: unsafe { MaybeUninit::uninit().assume_init() },
        }
    }
}

#[derive(Debug)]
struct Node16<K, V> {
    header: NodeHeader,
    children_count: u8,
    keys: [u8; 16],
    children: [MaybeUninit<Node<K, V>>; 16],
}

impl<K, V> Default for Node16<K, V> {
    fn default() -> Self {
        Node16 {
            header: NodeHeader::default(),
            children_count: 0,
            keys: [0; 16],
            // SAFETY: calling `assume_init` to convert an uninitialized array
            // into an array of uninitialized items is safe.
            children: unsafe { MaybeUninit::uninit().assume_init() },
        }
    }
}

impl<K, V> Indexed<K, V> for Node16<K, V> {
    fn header(&self) -> &NodeHeader {
        &self.header
    }

    fn get_child(&self, key: u8) -> Option<&Node<K, V>> {
        let mut l = 0;
        let mut r = self.children_count;
        while l < r {
            let m = (l + r) / 2;
            match self.keys[m as usize].cmp(&key) {
                std::cmp::Ordering::Less => l = m + 1,
                std::cmp::Ordering::Greater => r = m,
                std::cmp::Ordering::Equal => {
                    // SAFETY: If we found a matching key, then the corresponding
                    // child must have been initialized.
                    let child = unsafe { self.children[m as usize].assume_init_ref() };
                    return Some(child);
                }
            }
        }
        None
    }

    fn set_child(&mut self, key: u8, child: Node<K, V>) -> bool {
        if self.children_count >= 16 {
            return false;
        }
        let mut l = 0;
        let mut r = self.children_count;
        while l < r {
            let m = (l + r) / 2;
            match self.keys[m as usize].cmp(&key) {
                std::cmp::Ordering::Less => l = m + 1,
                std::cmp::Ordering::Greater => r = m,
                std::cmp::Ordering::Equal => l = m,
            }
        }
        let idx = l as usize;
        self.children_count += 1;
        self.keys[idx..].rotate_right(1);
        self.keys[idx] = key;
        self.children[idx..].rotate_right(1);
        self.children[idx].write(child);
        true
    }
}

#[derive(Debug)]
struct Node48<K, V> {
    header: NodeHeader,
    children_count: u8,
    indices: [Option<u8>; 256],
    children: [MaybeUninit<Node<K, V>>; 48],
}

impl<K, V> Default for Node48<K, V> {
    fn default() -> Self {
        Self {
            header: NodeHeader::default(),
            children_count: 0,
            indices: [None; 256],
            // SAFETY: calling `assume_init` to convert an uninitialized array
            // into an array of uninitialized items is safe.
            children: unsafe { MaybeUninit::uninit().assume_init() },
        }
    }
}

impl<K, V> Indexed<K, V> for Node48<K, V> {
    fn header(&self) -> &NodeHeader {
        &self.header
    }

    fn get_child(&self, key: u8) -> Option<&Node<K, V>> {
        self.indices[key as usize].map(|idx| {
            // SAFETY: If the found index is less than the number of children, then
            // the corresponding child must have been initialized.
            unsafe { self.children[idx as usize].assume_init_ref() }
        })
    }

    fn set_child(&mut self, key: u8, child: Node<K, V>) -> bool {
        if self.children_count >= 48 {
            return false;
        }
        let idx = self.children_count;
        self.children_count += 1;
        self.indices[key as usize] = Some(idx);
        self.children[idx as usize].write(child);
        true
    }
}

#[derive(Debug)]
struct Node256<K, V> {
    header: NodeHeader,
    children: [Option<Node<K, V>>; 256],
}

impl<K, V> Default for Node256<K, V> {
    fn default() -> Self {
        Self {
            header: NodeHeader::default(),
            children: [Self::DEFAULT_CHILD; 256],
        }
    }
}

impl<K, V> Indexed<K, V> for Node256<K, V> {
    fn header(&self) -> &NodeHeader {
        &self.header
    }

    fn get_child(&self, key: u8) -> Option<&Node<K, V>> {
        self.children[key as usize].as_ref()
    }

    fn set_child(&mut self, key: u8, child: Node<K, V>) -> bool {
        self.children[key as usize] = Some(child);
        true
    }
}

impl<K, V> Node256<K, V> {
    const DEFAULT_CHILD: Option<Node<K, V>> = None;
}

impl Comparable for u8 {
    type Target<'a> = [u8; 1];

    fn bytes(&self) -> Self::Target<'static> {
        self.to_be_bytes()
    }
}

trait Comparable {
    type Target<'a>: 'a + AsRef<[u8]>
    where
        Self: 'a;

    fn bytes(&self) -> Self::Target<'_>;
}

impl Comparable for u16 {
    type Target<'a> = [u8; 2];

    fn bytes(&self) -> Self::Target<'static> {
        self.to_be_bytes()
    }
}

impl Comparable for u32 {
    type Target<'a> = [u8; 4];

    fn bytes(&self) -> Self::Target<'static> {
        self.to_be_bytes()
    }
}

impl Comparable for u64 {
    type Target<'a> = [u8; 8];

    fn bytes(&self) -> Self::Target<'static> {
        self.to_be_bytes()
    }
}

impl Comparable for u128 {
    type Target<'a> = [u8; 16];

    fn bytes(&self) -> Self::Target<'static> {
        self.to_be_bytes()
    }
}

impl Comparable for i8 {
    type Target<'a> = [u8; 1];

    fn bytes(&self) -> Self::Target<'static> {
        let flipped = self ^ (1 << 7);
        flipped.to_be_bytes()
    }
}

impl Comparable for i16 {
    type Target<'a> = [u8; 2];

    fn bytes(&self) -> Self::Target<'static> {
        let flipped = self ^ (1 << 15);
        flipped.to_be_bytes()
    }
}

impl Comparable for i32 {
    type Target<'a> = [u8; 4];

    fn bytes(&self) -> Self::Target<'static> {
        let flipped = self ^ (1 << 31);
        flipped.to_be_bytes()
    }
}

impl Comparable for i64 {
    type Target<'a> = [u8; 8];

    fn bytes(&self) -> Self::Target<'static> {
        let flipped = self ^ (1 << 63);
        flipped.to_be_bytes()
    }
}

impl Comparable for i128 {
    type Target<'a> = [u8; 16];

    fn bytes(&self) -> Self::Target<'static> {
        let flipped = self ^ (1 << 127);
        flipped.to_be_bytes()
    }
}

impl Comparable for String {
    type Target<'a> = &'a [u8];

    fn bytes(&self) -> Self::Target<'_> {
        self.as_bytes()
    }
}

impl Comparable for Vec<u8> {
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
    fn test_node16_set_child() {
        let mut node = Node16::<usize, usize>::default();
        for i in 0..16 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
        }
        assert!(!node.set_child(16, Node::leaf(16, 16)));
    }

    #[test]
    fn test_node16_get_child() {
        let mut node = Node16::<usize, usize>::default();
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
    fn test_node48_set_child() {
        let mut node = Node48::<usize, usize>::default();
        for i in 0..48 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
        }
        assert!(!node.set_child(48, Node::leaf(48, 48)));
    }

    #[test]
    fn test_node48_get_child() {
        let mut node = Node48::<usize, usize>::default();
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
    fn test_node256_set_child() {
        let mut node = Node256::<usize, usize>::default();
        for i in 0..=255 {
            assert!(node.set_child(i, Node::leaf(i as usize, i as usize)));
        }
        assert!(node.set_child(255, Node::leaf(256, 256)));
    }

    #[test]
    fn test_node256_get_child() {
        let mut node = Node256::<usize, usize>::default();
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
