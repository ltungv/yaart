use ops::Insertion;
use raw::Leaf;
use raw::OpaqueNodePtr;

mod compressed_path;
mod key;
mod ops;
mod raw;
mod search_key;
mod tagged_ptr;

use raw::NodePtr;

pub use key::*;

/// A trait that seals other traits to disallow them from being implemented by external
/// modules/crates.
trait Sealed {}

/// An ordered map backed by an adaptive radix tree.
#[derive(Debug)]
pub struct RadixTreeMap<K, V, const PARTIAL_LEN: usize = 8> {
    state: Option<NonEmptyRadixTree<K, V, PARTIAL_LEN>>,
}

impl<K, V, const PARTIAL_LEN: usize> Default for RadixTreeMap<K, V, PARTIAL_LEN> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V, const PARTIAL_LEN: usize> RadixTreeMap<K, V, PARTIAL_LEN> {
    /// Creates a new empty tree.
    #[must_use]
    pub const fn new() -> Self {
        Self { state: None }
    }

    /// Inserts a key-value pair into the map.
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: BytesRepr,
    {
        if let Some(state) = &mut self.state {
            let inserted = unsafe { Insertion::prepare(state.root, key.repr()).apply(key, value) };
            state.root = inserted.root;
            inserted.prev.map(|l| l.value)
        } else {
            self.state = Some(NonEmptyRadixTree {
                root: NodePtr::alloc(Leaf::new(key, value)).as_opaque(),
            });
            None
        }
    }
}

#[derive(Debug)]
struct NonEmptyRadixTree<K, V, const PARTIAL_LEN: usize> {
    root: OpaqueNodePtr<K, V, PARTIAL_LEN>,
}

#[cfg(test)]
mod tests {
    use super::RadixTreeMap;

    #[test]
    fn test() {
        let mut m = RadixTreeMap::<Vec<u8>, usize, 4>::new();
        m.insert(b"abcdef_0".to_vec(), 0);
        m.insert(b"abcdef_1".to_vec(), 0);
        m.insert(b"abcxyz".to_vec(), 0);
    }
}
