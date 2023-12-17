use crate::static_vec::StaticVec;

const MAX_PREFIX_LEN: usize = 6;

trait Indexed<K, V> {
    fn prefix_len(&self) -> usize;
    fn check_prefix(&self, key: &[u8]) -> bool;
    fn find_child(&self, key: u8) -> Option<&Node<K, V>>;
}

trait Comparable {
    type Target<'a>: 'a + AsRef<[u8]>
    where
        Self: 'a;

    fn bytes(&self) -> Self::Target<'_>;
}

/// Count the number of matching elements at the beginning of two slices.
fn common_prefix_length<T>(lhs: &[T], rhs: &[T]) -> usize
where
    T: PartialEq,
{
    lhs.iter()
        .zip(rhs.iter())
        .take_while(|(x, y)| x.eq(y))
        .count()
}

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

    fn node4() -> Node<K, V> {
        Node::Node4(Box::default())
    }

    fn node16() -> Node<K, V> {
        Node::Node16(Box::default())
    }

    fn node48() -> Node<K, V> {
        Node::Node48(Box::default())
    }

    fn node256() -> Node<K, V> {
        Node::Node256(Box::default())
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

    fn search_inner(&self, key: &[u8], offset: usize) -> Option<&V> {
        match self {
            Node::Leaf(node) => {
                let leaf_key = node.key.bytes();
                if key == leaf_key.as_ref() {
                    Some(&node.value)
                } else {
                    None
                }
            }
            Node::Node4(node) => Self::search_child(node.as_ref(), key, offset),
            Node::Node16(node) => Self::search_child(node.as_ref(), key, offset),
            Node::Node48(node) => Self::search_child(node.as_ref(), key, offset),
            Node::Node256(node) => Self::search_child(node.as_ref(), key, offset),
        }
    }

    fn search_child<'a, N>(node: &'a N, key: &[u8], offset: usize) -> Option<&'a V>
    where
        K: 'a,
        N: Indexed<K, V>,
    {
        if node.check_prefix(&key[offset..]) {
            return None;
        }
        let new_offset = offset + node.prefix_len();
        node.find_child(key[new_offset])
            .and_then(|child| child.search_inner(key, new_offset + 1))
    }

    fn insert(&mut self, key: K, value: V) {
        self.insert_inner(key, value, 0)
    }

    fn insert_inner(&mut self, key: K, value: V, offset: usize) {
        let node  = match self {
            Node::Leaf(leaf) => {
                // NOTE: Create a scope here so `key_bytes` is dropped before
                // we take `key`.
                let insert_key_bytes = key.bytes();
                let leaf_key_bytes = leaf.key.bytes();
                if insert_key_bytes.as_ref() == leaf_key_bytes.as_ref() {
                    leaf.value = value;
                    return;
                }

                let prefix_len =
                    common_prefix_length(insert_key_bytes.as_ref(), leaf_key_bytes.as_ref());

                let mut new_node4 = Node4::<K, V>::default();
                for b in insert_key_bytes.as_ref().iter().take(prefix_len) {
                    if new_node4.prefix.push_within_capacity(*b).is_err() {
                        break;
                    }
                }

                let child_key1 = leaf_key_bytes.as_ref()[offset + prefix_len];
                let child_key2 = insert_key_bytes.as_ref()[offset + prefix_len];

                drop(insert_key_bytes);
                let new_leaf = Node::leaf(key, value);
                Node::Node4(Box::new(new_node4));
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
    key: K,
    value: V,
}

#[derive(Debug)]
struct Node4<K, V> {
    prefix: StaticVec<u8, MAX_PREFIX_LEN>,
    keys: StaticVec<u8, 4>,
    children: [Option<Node<K, V>>; 4],
}

impl<K, V> Default for Node4<K, V> {
    fn default() -> Self {
        Self {
            prefix: StaticVec::default(),
            keys: StaticVec::default(),
            children: [Node4::<K, V>::NODE_DEFAULT; 4],
        }
    }
}

impl<K, V> Indexed<K, V> for Node4<K, V> {
    fn prefix_len(&self) -> usize {
        self.prefix.len()
    }

    fn check_prefix(&self, key: &[u8]) -> bool {
        common_prefix_length(self.prefix.as_ref(), key) == self.prefix.len()
    }

    fn find_child(&self, key: u8) -> Option<&Node<K, V>> {
        self.keys
            .search_linear(&key)
            .and_then(|idx| self.children[idx].as_ref())
    }
}

impl<K, V> Node4<K, V> {
    const NODE_DEFAULT: Option<Node<K, V>> = None;
}

#[derive(Debug)]
struct Node16<K, V> {
    prefix: StaticVec<u8, MAX_PREFIX_LEN>,
    keys: StaticVec<u8, 16>,
    children: [Option<Node<K, V>>; 16],
}

impl<K, V> Default for Node16<K, V> {
    fn default() -> Self {
        Self {
            prefix: StaticVec::default(),
            keys: StaticVec::default(),
            children: [Node16::<K, V>::NODE_DEFAULT; 16],
        }
    }
}

impl<K, V> Indexed<K, V> for Node16<K, V> {
    fn prefix_len(&self) -> usize {
        self.prefix.len()
    }

    fn check_prefix(&self, key: &[u8]) -> bool {
        common_prefix_length(self.prefix.as_ref(), key) == self.prefix.len()
    }

    fn find_child(&self, key: u8) -> Option<&Node<K, V>> {
        self.keys
            .search_linear(&key)
            .and_then(|idx| self.children[idx].as_ref())
    }
}

impl<K, V> Node16<K, V> {
    const NODE_DEFAULT: Option<Node<K, V>> = None;
}

#[derive(Debug)]
struct Node48<K, V> {
    prefix: StaticVec<u8, MAX_PREFIX_LEN>,
    indices: [u8; 256],
    children: [Option<Node<K, V>>; 48],
}

impl<K, V> Default for Node48<K, V> {
    fn default() -> Self {
        Self {
            prefix: StaticVec::default(),
            indices: [0; 256],
            children: [Node48::<K, V>::NODE_DEFAULT; 48],
        }
    }
}

impl<K, V> Indexed<K, V> for Node48<K, V> {
    fn prefix_len(&self) -> usize {
        self.prefix.len()
    }

    fn check_prefix(&self, key: &[u8]) -> bool {
        common_prefix_length(self.prefix.as_ref(), key) == self.prefix.len()
    }

    fn find_child(&self, key: u8) -> Option<&Node<K, V>> {
        let idx = self.indices[key as usize];
        self.children[idx as usize].as_ref()
    }
}

impl<K, V> Node48<K, V> {
    const NODE_DEFAULT: Option<Node<K, V>> = None;
}

#[derive(Debug)]
struct Node256<K, V> {
    prefix: StaticVec<u8, MAX_PREFIX_LEN>,
    children: [Option<Node<K, V>>; 256],
}

impl<K, V> Default for Node256<K, V> {
    fn default() -> Self {
        Self {
            prefix: StaticVec::default(),
            children: [Node256::<K, V>::NODE_DEFAULT; 256],
        }
    }
}

impl<K, V> Indexed<K, V> for Node256<K, V> {
    fn prefix_len(&self) -> usize {
        self.prefix.len()
    }

    fn check_prefix(&self, key: &[u8]) -> bool {
        common_prefix_length(self.prefix.as_ref(), key) == self.prefix.len()
    }

    fn find_child(&self, key: u8) -> Option<&Node<K, V>> {
        self.children[key as usize].as_ref()
    }
}

impl<K, V> Node256<K, V> {
    const NODE_DEFAULT: Option<Node<K, V>> = None;
}

impl Comparable for u8 {
    type Target<'a> = [u8; 1];

    fn bytes(&self) -> Self::Target<'static> {
        self.to_be_bytes()
    }
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
