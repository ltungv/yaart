use raw::Leaf;
use raw::OpaqueNodePtr;

mod compressed_path;
mod key;
mod raw;
mod search_key;
mod tagged_ptr;

use raw::NodePtr;

pub(crate) trait Sealed {}

struct RadixTreeMap<K, V, const PARTIAL_LEN: usize = 8> {
    state: Option<NonEmptyRadixTree<K, V, PARTIAL_LEN>>,
}

impl<K, V, const PARTIAL_LEN: usize> RadixTreeMap<K, V, PARTIAL_LEN> {
    fn new() -> Self {
        Self { state: None }
    }

    fn insert(&mut self, key: K, value: V) -> Option<V> {
        if let Some(_) = self.state {
            None
        } else {
            let leaf = NodePtr::alloc(Leaf::new(key, value));
            let state = NonEmptyRadixTree { root: leaf.into() };
            self.state = Some(state);
            None
        }
    }
}

struct NonEmptyRadixTree<K, V, const PARTIAL_LEN: usize> {
    root: OpaqueNodePtr<K, V, PARTIAL_LEN>,
}

pub struct InsertPoint {}

pub struct DeletePoint {}
