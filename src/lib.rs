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
#![allow(edition_2024_expr_fragment_specifier, clippy::too_many_lines, clippy::type_complexity)]

mod compressed_path;
mod ops;
mod raw;
mod repr;
mod search_key;
mod tagged_ptr;

#[doc(hidden)]
pub mod test_common;

use std::{borrow::Borrow, fmt, num::NonZeroUsize};

use ops::{Delete, Fmt, Insert, Ptr, Search};
use raw::{Leaf, NodePtr, OpaqueNodePtr};

pub use repr::*;
pub use search_key::*;

/// A trait that seals other traits to disallow them from being implemented by external
/// modules/crates.
trait Sealed {}

/// An ordered map backed by an adaptive radix tree.
pub struct RadixTreeMap<K, V, const PARTIAL_LEN: usize = 8> {
    state: Option<NonEmptyRadixTreeMap<K, V, PARTIAL_LEN>>,
}

impl<K, V, const PARTIAL_LEN: usize> Drop for RadixTreeMap<K, V, PARTIAL_LEN> {
    fn drop(&mut self) {
        if let Some(state) = &self.state {
            unsafe {
                Ptr::dealloc(state.root);
            }
        }
    }
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
        self.state.as_ref().map_or(0, NonEmptyRadixTreeMap::len)
    }

    /// Inserts a key-value pair into the map.
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: BytesRepr,
    {
        let Some(state) = &mut self.state else {
            self.state = Some(NonEmptyRadixTreeMap::new(Leaf::new(key, value)));
            return None;
        };
        state.insert(key, value)
    }

    /// Removes a key-value pari from the map given the key.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
    where
        K: BytesRepr + Borrow<Q>,
        Q: BytesRepr + ?Sized,
    {
        let Some(state) = &mut self.state else {
            return None;
        };
        match state.remove(key) {
            Removal::None => None,
            Removal::Some(v) => Some(v),
            Removal::Last(v) => {
                self.state = None;
                Some(v)
            }
        }
    }

    /// Gets a key-value pair from the map given the key.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: BytesRepr + Borrow<Q>,
        Q: BytesRepr + ?Sized,
    {
        self.state.as_ref().and_then(|s| s.get(key))
    }

    /// Gets the first key-value pair from the map.
    #[must_use]
    pub fn first_key_value(&self) -> Option<(&K, &V)>
    where
        K: OrderedBytesRepr,
    {
        self.state.as_ref().map(|s| {
            let leaf = s.first();
            (&leaf.key, &leaf.value)
        })
    }

    /// Gets the last key-value pair from the map.
    #[must_use]
    pub fn last_key_value(&self) -> Option<(&K, &V)>
    where
        K: OrderedBytesRepr,
    {
        self.state.as_ref().map(|s| {
            let leaf = s.last();
            (&leaf.key, &leaf.value)
        })
    }
}

enum Removal<T> {
    None,
    Some(T),
    Last(T),
}

#[derive(Debug)]
struct NonEmptyRadixTreeMap<K, V, const PARTIAL_LEN: usize> {
    len: NonZeroUsize,
    root: OpaqueNodePtr<K, V, PARTIAL_LEN>,
}

impl<K, V, const PARTIAL_LEN: usize> NonEmptyRadixTreeMap<K, V, PARTIAL_LEN> {
    fn new(leaf: Leaf<K, V>) -> Self {
        Self { len: unsafe { NonZeroUsize::new_unchecked(1) }, root: NodePtr::alloc(leaf).as_opaque() }
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

    fn remove<Q>(&mut self, key: &Q) -> Removal<V>
    where
        K: BytesRepr + Borrow<Q>,
        Q: BytesRepr + ?Sized,
    {
        let Some(delete) = (unsafe { Delete::prepare(self.root, key.repr()) }) else {
            // No leaf was found with a matching key so nothing is removed.
            return Removal::None;
        };
        let deleted = unsafe { delete.apply(self.root) };
        let Some(root) = deleted.root else {
            // The root was removed after the deletion.
            assert_eq!(self.len(), 1);
            return Removal::Last(deleted.leaf.value);
        };
        // The root was retained or updated after the deletion.
        assert_ne!(self.len(), 1);
        let new_len = self.len() - 1;
        self.len = NonZeroUsize::new(new_len).expect("index is non-zero");
        self.root = root;
        Removal::Some(deleted.leaf.value)
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

    fn first(&self) -> &Leaf<K, V>
    where
        K: OrderedBytesRepr,
    {
        let leaf_ptr = unsafe { Search::minimum(self.root) };
        unsafe { leaf_ptr.as_ref() }
    }

    fn last(&self) -> &Leaf<K, V>
    where
        K: OrderedBytesRepr,
    {
        let leaf_ptr = unsafe { Search::maximum(self.root) };
        unsafe { leaf_ptr.as_ref() }
    }
}

#[cfg(test)]
mod tests {
    use crate::test_common::get_samples;

    use super::RadixTreeMap;

    #[test]
    fn it_works() {
        let samples = get_samples(rand::random(), 4, 2..14, 4, 8);
        let mut art = RadixTreeMap::<String, usize>::new();

        assert!(art.is_empty());
        for (idx, word) in samples.clone().into_iter().enumerate() {
            art.insert(word, idx);
        }

        assert_eq!(art.len(), samples.len());
        for (idx, word) in samples.iter().enumerate() {
            assert_eq!(art.get(word), Some(&idx));
        }

        for (idx, word) in samples.iter().enumerate() {
            assert_eq!(art.remove(word), Some(idx));
        }
        assert!(art.is_empty());
    }

    #[cfg_attr(miri, ignore)]
    #[test]
    fn dict() {
        let words: Vec<_> = include_str!("../benches/data/dict.txt").lines().map(String::from).collect();
        let mut art = RadixTreeMap::<String, usize>::new();

        assert!(art.is_empty());
        for (idx, word) in words.clone().into_iter().enumerate() {
            art.insert(word, idx);
        }

        assert_eq!(art.len(), words.len());
        for (idx, word) in words.iter().enumerate() {
            assert_eq!(art.get(word), Some(&idx));
        }

        for (idx, word) in words.iter().enumerate() {
            assert_eq!(art.remove(word), Some(idx));
        }
        assert!(art.is_empty());
    }
}
