//! # Adaptive Radix Tree

#![deny(
    clippy::all,
    rust_2018_idioms,
    rust_2024_compatibility,
    rust_2021_compatibility,
    missing_debug_implementations,
    missing_docs
)]
#![warn(rustdoc::all, clippy::pedantic, clippy::nursery)]
#![allow(
    edition_2024_expr_fragment_specifier,
    clippy::too_many_lines,
    clippy::type_complexity
)]

use std::borrow::Borrow;
use std::fmt;
use std::num::NonZeroUsize;

use ops::Fmt;
use ops::Insert;
use ops::Ptr;
use ops::Search;
use raw::Leaf;
use raw::OpaqueNodePtr;

mod compressed_path;
mod ops;
mod raw;
mod repr;
mod search_key;
mod tagged_ptr;

use raw::NodePtr;

pub use repr::*;
pub use search_key::*;

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

    /// Returns whether the map is empty.
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.state.is_none()
    }

    /// Returns the number of existing entries in the map.
    #[must_use]
    pub fn len(&self) -> usize {
        self.state.as_ref().map_or(0, NonEmptyRadixTree::len)
    }

    /// Gets a key-value pair from the map given the key.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: BytesRepr + Borrow<Q>,
        Q: BytesRepr + ?Sized,
    {
        self.state.as_ref().and_then(|s| s.get(key))
    }

    /// Inserts a key-value pair into the map.
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: BytesRepr,
    {
        let Some(state) = &mut self.state else {
            self.state = Some(NonEmptyRadixTree::new(Leaf::new(key, value)));
            return None;
        };
        state.insert(key, value)
    }
}

#[derive(Debug)]
struct NonEmptyRadixTree<K, V, const PARTIAL_LEN: usize> {
    len: NonZeroUsize,
    root: OpaqueNodePtr<K, V, PARTIAL_LEN>,
}

impl<K, V, const PARTIAL_LEN: usize> Drop for NonEmptyRadixTree<K, V, PARTIAL_LEN> {
    fn drop(&mut self) {
        unsafe {
            Ptr::dealloc(self.root);
        }
    }
}

impl<K, V, const PARTIAL_LEN: usize> NonEmptyRadixTree<K, V, PARTIAL_LEN> {
    fn new(leaf: Leaf<K, V>) -> Self {
        Self {
            len: unsafe { NonZeroUsize::new_unchecked(1) },
            root: NodePtr::alloc(leaf).as_opaque(),
        }
    }

    fn len(&self) -> usize {
        usize::from(self.len)
    }

    fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: BytesRepr,
    {
        let inserted = unsafe { Insert::prepare(self.root, key.repr()).apply(key, value) };
        let Some(len) = self.len.checked_add(usize::from(inserted.prev.is_none())) else {
            unreachable!("index overflows");
        };
        self.len = len;
        self.root = inserted.root;
        inserted.prev.map(|l| l.value)
    }

    fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: BytesRepr + Borrow<Q>,
        Q: BytesRepr + ?Sized,
    {
        let leaf_ptr = unsafe { Search::exact(self.root, key.repr())? };
        let leaf = unsafe { leaf_ptr.as_ref() };
        Some(&leaf.value)
    }
}

#[cfg(test)]
mod tests {
    use super::RadixTreeMap;

    #[cfg_attr(miri, ignore)]
    #[test]
    fn test() {
        let words = include_str!("../benches/data/medium-dict.txt");
        let mut bytes = 0;
        let mut words: Vec<_> = words
            .lines()
            .map(|s| {
                let s = String::from(s);
                bytes += s.len();
                s
            })
            .collect();

        words.dedup();
        words.sort();

        let mut art = RadixTreeMap::<String, usize>::new();
        for (idx, word) in words.clone().into_iter().enumerate() {
            art.insert(word, idx);
        }
        for (idx, word) in words.into_iter().enumerate() {
            assert_eq!(art.get(&word), Some(&idx));
        }
    }
}
