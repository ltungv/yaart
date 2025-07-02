use std::borrow::Borrow;
use std::fmt;
use std::num::NonZeroUsize;

use ops::Fmt;
use ops::Insert;
use ops::Search;
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
pub struct RadixTreeMap<K, V, const PARTIAL_LEN: usize = 8> {
    state: Option<NonEmptyRadixTree<K, V, PARTIAL_LEN>>,
}

impl<K, V, const PARTIAL_LEN: usize> Default for RadixTreeMap<K, V, PARTIAL_LEN> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V, const PARTIAL_LEN: usize> fmt::Debug for RadixTreeMap<K, V, PARTIAL_LEN>
where
    K: BytesRepr,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Some(state) = &self.state else {
            return write!(f, "<EMPTY>");
        };
        unsafe { Fmt::debug(state.root, f) }
    }
}

impl<K, V, const PARTIAL_LEN: usize> RadixTreeMap<K, V, PARTIAL_LEN> {
    /// Creates a new empty map.
    #[must_use]
    pub const fn new() -> Self {
        Self { state: None }
    }

    /// Returns the number of existing entries in the map.
    #[must_use]
    pub fn len(&self) -> usize {
        let Some(s) = &self.state else {
            return 0;
        };
        usize::from(s.len)
    }

    /// Returns whether the map is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets a key-value pair from the map given the key.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: BytesRepr + Borrow<Q>,
        Q: BytesRepr + ?Sized,
    {
        let Some(state) = &self.state else {
            return None;
        };
        let leaf_ptr = unsafe { Search::exact(state.root, key.repr())? };
        let leaf = unsafe { leaf_ptr.as_ref() };
        Some(&leaf.value)
    }

    /// Inserts a key-value pair into the map.
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: BytesRepr,
    {
        let Some(state) = &mut self.state else {
            self.state = Some(NonEmptyRadixTree {
                len: unsafe { NonZeroUsize::new_unchecked(1) },
                root: NodePtr::alloc(Leaf::new(key, value)).as_opaque(),
            });
            return None;
        };
        let inserted = unsafe { Insert::prepare(state.root, key.repr()).apply(key, value) };
        let Some(len) = state.len.checked_add(usize::from(inserted.prev.is_none())) else {
            unreachable!("index overflows");
        };
        state.len = len;
        state.root = inserted.root;
        inserted.prev.map(|l| l.value)
    }
}

#[derive(Debug)]
struct NonEmptyRadixTree<K, V, const PARTIAL_LEN: usize> {
    len: NonZeroUsize,
    root: OpaqueNodePtr<K, V, PARTIAL_LEN>,
}

#[cfg(test)]
mod tests {
    use super::RadixTreeMap;

    #[test]
    fn test() {
        let mut m = RadixTreeMap::<Vec<u8>, usize, 4>::new();
        m.insert(b"abcdef_0".to_vec(), 1);
        m.insert(b"abcdef_1".to_vec(), 2);
        m.insert(b"abcxyz".to_vec(), 3);

        assert_eq!(m.get(b"abcdef_0".as_slice()), Some(&1));
        assert_eq!(m.get(b"abcdef_1".as_slice()), Some(&2));
        assert_eq!(m.get(b"abcxyz".as_slice()), Some(&3));

        println!("{m:?}");
    }
}
