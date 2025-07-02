mod header;
mod inner256;
mod inner48;
mod inner_sorted;
mod leaf;
mod ptr;

use crate::Sealed;

pub use header::*;
pub use inner256::*;
pub use inner48::*;
pub use inner_sorted::*;
pub use leaf::*;
pub use ptr::*;

use super::{
    ops::{FullPrefixMismatch, PrefixMatch, PrefixMismatch, Search},
    repr::BytesRepr,
    search_key::SearchKey,
};

/// An enum of all node types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum NodeType {
    /// A leaf node.
    Leaf = 0,
    /// An inner node that can hold a maximum of 4 children.
    Inner4 = 1,
    /// An inner node that can hold a maximum of 16 children.
    Inner16 = 2,
    /// An inner node that can hold a maximum of 48 children.
    Inner48 = 3,
    /// An inner node that can hold a maximum of 256 children.
    Inner256 = 4,
}

// NOTE: We want `Node` to extend `Sealed`, which is private to the crate, to limit the number of
// type that can implement `Node`.
/// Every type of node in a tree implements this trait.
#[allow(private_bounds)]
pub trait Node<const PARTIAL_LEN: usize>: Sealed {
    /// The runtime type of the node.
    const TYPE: NodeType;
    /// The key type carried by the leaf nodes
    type Key;
    /// The value type carried by the leaf nodes
    type Value;
}

/// Every type of inner node in a tree implements this trait.
pub trait Inner<const PARTIAL_LEN: usize>: Node<PARTIAL_LEN> {
    /// The type of the next larger node type.
    type GrownNode: Inner<PARTIAL_LEN, Key = Self::Key, Value = Self::Value>;

    /// The type of the next smaller node type.
    type ShrunkNode: Inner<PARTIAL_LEN, Key = Self::Key, Value = Self::Value>;

    type Iter<'a>: Iterator<Item = (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>)>
        + DoubleEndedIterator
        + ExactSizeIterator
    where
        Self: 'a;

    /// Grows this node into the next larger type, copying over children and prefix information.
    fn grow(&self) -> Self::GrownNode;

    /// Shrinks this node into the next smaller class, copying over children and prefix
    /// information.
    fn shrink(&self) -> Self::ShrunkNode;

    fn iter(&self) -> Self::Iter<'_>;

    /// Returns the header of this node.
    fn header(&self) -> &Header<PARTIAL_LEN>;

    /// Adds a child pointer with a key partial to this node.
    fn add(
        &mut self,
        partial_key: u8,
        child_ptr: OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>,
    );

    /// Deletes a child pointer at the key partial from this node.
    fn del(
        &mut self,
        partial_key: u8,
    ) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>>;

    /// Gets a child pointer that corresponds to the given key partial.
    fn get(&self, partial_key: u8) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>>;

    /// Returns the minimum child pointer of this node and it's key
    fn min(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>);

    /// Returns the maximum child pointer of this inner and it's key
    fn max(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>);

    fn is_full(&self) -> bool {
        match Self::TYPE {
            NodeType::Leaf => unreachable!("invalid inner node type"),
            NodeType::Inner4 => self.header().children >= 4,
            NodeType::Inner16 => self.header().children >= 16,
            NodeType::Inner48 => self.header().children >= 48,
            NodeType::Inner256 => self.header().children >= 256,
        }
    }

    /// Reads the full prefix of this node, and searches a descendant leaf node to find implicit
    /// bytes if necessary.
    fn read_full_prefix(
        &self,
        current_depth: usize,
    ) -> (SearchKey<'_>, Option<NodePtr<Leaf<Self::Key, Self::Value>>>)
    where
        Self::Key: BytesRepr,
    {
        let header = self.header();
        if header.path.prefix_len() <= PARTIAL_LEN {
            // The remaining prefix is contained within the compressed path.
            (SearchKey::new(header.path.as_partial_prefix()), None)
        } else {
            // Find the minimum leaf which is guaranteed to have the full prefix of this node.
            let leaf_ptr = unsafe { Search::minimum(self.min().1) };
            let leaf = unsafe { leaf_ptr.as_ref() };
            let prefix = leaf
                .key
                .repr()
                .range(current_depth, header.path.prefix_len());
            (prefix, Some(leaf_ptr))
        }
    }

    /// Compares the compressed path of a node with the key and returns the number of equal bytes.
    ///
    /// The full prefix for this node will be read, even if a descendant leaf node needs to be
    /// searched to find implicit bytes.
    fn match_full_prefix(
        &self,
        key: SearchKey<'_>,
        current_depth: usize,
    ) -> Result<usize, FullPrefixMismatch<Self::Key, Self::Value, PARTIAL_LEN>>
    where
        Self::Key: BytesRepr,
    {
        // Reads the full prefix of this node.
        let (prefix, leaf) = self.read_full_prefix(current_depth);
        let prefix_len = prefix.common_prefix_len(key.shift(current_depth));

        assert!(prefix_len <= prefix.len());

        if prefix_len < prefix.len() {
            // The common prefix with the seach key is shorter than the actual prefix.
            return Err(FullPrefixMismatch {
                prefix_len,
                mismatched: prefix[prefix_len],
                leaf,
            });
        }
        Ok(prefix_len)
    }

    /// Attemps to match pessimistically when the partial prefix is contained within this node.
    /// Otherwise, matches optimistically.
    ///
    /// In the case of an error, the caller can determine which match strategy was used based on
    /// the [`mismatched`] field in [`PrefixMismatch`]. When it's [`None`], optimistic match was
    /// used, otherwise, optimistic match was used.
    fn match_partial_prefix(&self, key: SearchKey<'_>) -> Result<PrefixMatch, PrefixMismatch> {
        let matched = if self.header().path.prefix_len() > PARTIAL_LEN {
            let prefix_len = self.match_optimistic(key)?;
            PrefixMatch::Optimistic(prefix_len)
        } else {
            let prefix_len = self.match_pessimistic(key)?;
            PrefixMatch::Pessimistic(prefix_len)
        };
        Ok(matched)
    }

    /// Compares the given key's length and this node's length to find for a mismatch. In this
    /// case, a mismatch just means the key at the current depth is not long enough to match with
    /// the prefix. Once we arrive at a leaf, a full comparison must be made between the leaf's key
    /// and the given key.
    fn match_optimistic(&self, key: SearchKey<'_>) -> Result<usize, PrefixMismatch> {
        let key_len = key.len();
        let prefix_len = self.header().path.prefix_len();
        if key_len < prefix_len {
            return Err(PrefixMismatch {
                prefix_len: key_len,
                mismatched: None,
            });
        }
        Ok(prefix_len)
    }

    /// Fully compares the given key and this node's partial prefix to find for a mismatch. If we
    /// reach a leaf using only pessimistic matches, the leaf can be returned immediately without
    /// any further check.
    fn match_pessimistic(&self, key: SearchKey<'_>) -> Result<usize, PrefixMismatch> {
        let partial_prefix = SearchKey::new(self.header().path.as_partial_prefix());
        let prefix_len = partial_prefix.common_prefix_len(key);
        if prefix_len < self.header().path.prefix_len() {
            return Err(PrefixMismatch {
                prefix_len,
                mismatched: Some(partial_prefix[prefix_len]),
            });
        }
        Ok(prefix_len)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        compressed_path::CompressedPath,
        raw::{ptr::tests::NodePtrGuard, Inner256, Inner48},
        search_key::SearchKey,
    };

    use super::{Header, Inner, InnerSorted, Leaf};

    #[should_panic = "grow is impossible"]
    #[test]
    fn grow_inner256() {
        let inner = Inner256::<u64, u64, 8>::from(Header::from(CompressedPath::default()));
        inner.grow();
    }

    #[should_panic = "shrink is impossible"]
    #[test]
    fn shrink_inner4() {
        let inner = InnerSorted::<u64, u64, 8, 4>::from(Header::from(CompressedPath::default()));
        inner.shrink();
    }

    macro_rules! test_inner_grow {
        ($name:ident,$T:ty,$max_partial_key:expr,$grown_max_partial_key:expr) => {
            #[test]
            fn $name() {
                let max_partial_key = $max_partial_key as u8;
                let grown_max_partial_key = $grown_max_partial_key as u8;
                let mut leaves = NodePtrGuard::new();
                for i in 0..=grown_max_partial_key {
                    leaves.manage(Leaf::new(i as usize, i as usize));
                }

                let mut inner = <$T>::from(Header::from(CompressedPath::default()));
                for i in 0..=max_partial_key {
                    inner.add(i, leaves[i as usize].into());
                }

                assert!(inner.is_full());
                let mut grown = inner.grow();

                assert!(!grown.is_full());
                for i in max_partial_key + 1..=grown_max_partial_key {
                    grown.add(i, leaves[i as usize].into());
                    assert_eq!(grown.header().children, u16::from(i) + 1)
                }

                assert!(grown.is_full());
                for i in 0..=grown_max_partial_key {
                    assert_eq!(grown.get(i), Some(leaves[i as usize].into()))
                }
            }
        };
    }

    macro_rules! test_inner_shrink {
        ($name:ident,$T:ty,$max_partial_key:expr) => {
            #[test]
            fn $name() {
                let max_partial_key = $max_partial_key as u8;
                let mut leaves = NodePtrGuard::new();
                for i in 0..=max_partial_key {
                    leaves.manage(Leaf::new(i as usize, i as usize));
                }

                let mut inner = <$T>::from(Header::from(CompressedPath::default()));
                for i in 0..=max_partial_key {
                    inner.add(i, leaves[i as usize].into());
                }

                assert!(!inner.is_full());
                let shrunk = inner.shrink();

                assert!(shrunk.is_full());
                for i in 0..=max_partial_key {
                    assert_eq!(shrunk.get(i), Some(leaves[i as usize].into()))
                }
            }
        };
    }

    macro_rules! test_inner_iter {
        ($name:ident,$T:ty,$max_partial_key:expr) => {
            #[test]
            fn $name() {
                let max_partial_key = $max_partial_key as u8;
                let mut leaves = NodePtrGuard::new();
                for i in 0..=max_partial_key {
                    leaves.manage(Leaf::new(i as usize, i as usize));
                }

                let mut inner = <$T>::from(Header::from(CompressedPath::default()));
                for i in 0..=max_partial_key {
                    inner.add(i, leaves[i as usize].into());
                }

                for (i, (key, child)) in inner.into_iter().enumerate() {
                    assert_eq!(key as usize, i);
                    assert_eq!(child, leaves[key as usize]);
                }

                for (i, (key, child)) in inner.into_iter().enumerate().rev() {
                    assert_eq!(key as usize, i);
                    assert_eq!(child, leaves[key as usize]);
                }
            }
        };
    }

    macro_rules! test_inner_add_and_get {
        ($name:ident,$T:ty,$max_partial_key:expr) => {
            #[test]
            fn $name() {
                let max_partial_key = $max_partial_key as u8;
                let mut leaves = NodePtrGuard::new();
                for i in 0..=max_partial_key {
                    leaves.manage(Leaf::new(i as usize, i as usize));
                }
                let mut inner = <$T>::from(Header::from(CompressedPath::default()));
                for i in 0..=max_partial_key {
                    inner.add(i, leaves[i as usize].into());
                    assert_eq!(inner.header().children, u16::from(i) + 1)
                }
                for i in 0..=max_partial_key {
                    assert_eq!(inner.get(i), Some(leaves[i as usize].into()))
                }
            }
        };
    }

    macro_rules! test_inner_add_and_del {
        ($name:ident,$T:ty,$max_partial_key:expr) => {
            #[test]
            fn $name() {
                let max_partial_key = $max_partial_key as u8;
                let mut inner = <$T>::from(Header::from(CompressedPath::default()));
                {
                    let mut leaves = NodePtrGuard::new();
                    for i in 0..=max_partial_key {
                        leaves.manage(Leaf::new(i as usize, i as usize));
                    }
                    for i in 0..=max_partial_key {
                        inner.add(i, leaves[i as usize].into());
                        assert_eq!(inner.header().children, u16::from(i) + 1)
                    }
                    for i in 0..=max_partial_key {
                        assert_eq!(inner.del(i), Some(leaves[i as usize].into()));
                        assert_eq!(inner.header().children, u16::from(max_partial_key - i));
                    }
                }
                {
                    let mut leaves = NodePtrGuard::new();
                    for i in 0..=max_partial_key {
                        leaves.manage(Leaf::new(i as usize, i as usize));
                    }
                    for i in 0..=max_partial_key {
                        inner.add(i, leaves[i as usize].into());
                        assert_eq!(inner.header().children, u16::from(i) + 1)
                    }
                    for i in 0..=max_partial_key {
                        assert_eq!(inner.get(i), Some(leaves[i as usize].into()))
                    }
                }
            }
        };
    }

    macro_rules! test_inner_add_existing {
        ($name:ident,$T:ty,$max_partial_key:expr) => {
            #[test]
            fn $name() {
                let max_partial_key = $max_partial_key as u8;
                let mut inner = <$T>::from(Header::from(CompressedPath::default()));
                {
                    let mut leaves = NodePtrGuard::new();
                    for i in 0..=max_partial_key {
                        leaves.manage(Leaf::new(i as usize, i as usize));
                    }
                    for i in 0u8..=max_partial_key {
                        inner.add(i, leaves[i as usize].into());
                        assert_eq!(inner.header().children, u16::from(i) + 1)
                    }
                    for i in 0u8..=max_partial_key {
                        assert_eq!(inner.get(i), Some(leaves[i as usize].into()))
                    }
                }
                {
                    let mut leaves = NodePtrGuard::new();
                    for i in 0..=max_partial_key {
                        leaves.manage(Leaf::new(i as usize, i as usize));
                    }
                    for i in 0u8..=max_partial_key {
                        inner.add(i, leaves[i as usize].into());
                        assert_eq!(inner.header().children, u16::from(max_partial_key) + 1)
                    }
                    for i in 0u8..=max_partial_key {
                        assert_eq!(inner.get(i), Some(leaves[i as usize].into()))
                    }
                }
            }
        };
    }

    macro_rules! test_inner_del_and_get {
        ($name:ident,$T:ty,$max_partial_key:expr) => {
            #[test]
            fn $name() {
                let max_partial_key = $max_partial_key as u8;
                let mut leaves = NodePtrGuard::new();
                for i in 0..=max_partial_key {
                    leaves.manage(Leaf::new(i as usize, i as usize));
                }
                let mut inner = <$T>::from(Header::from(CompressedPath::default()));
                for i in 0..=max_partial_key {
                    assert!(inner.del(i).is_none());
                }
                for i in 0..=max_partial_key {
                    inner.add(i, leaves[i as usize].into());
                }
                for i in 0..=max_partial_key {
                    let child = inner.del(i);
                    assert_eq!(child, Some(leaves[i as usize].into()));
                    let child = inner.get(i);
                    assert!(child.is_none());
                }
                assert_eq!(inner.header().children, 0);
            }
        };
    }

    macro_rules! test_inner_min {
        ($name:ident,$T:ty,$max_partial_key:expr) => {
            #[test]
            fn $name() {
                let max_partial_key = $max_partial_key as u8;
                let mut leaves = NodePtrGuard::new();
                for i in 0..=max_partial_key {
                    leaves.manage(Leaf::new(i as usize, i as usize));
                }
                let mut inner = <$T>::from(Header::from(CompressedPath::default()));
                for i in (0..=max_partial_key).rev() {
                    inner.add(i, leaves[i as usize].into());
                    let min_child = inner.min();
                    assert_eq!(min_child, (i, leaves[i as usize].into()));
                }
            }
        };
    }

    macro_rules! test_inner_max {
        ($name:ident,$T:ty,$max_partial_key:expr) => {
            #[test]
            fn $name() {
                let max_partial_key = $max_partial_key as u8;
                let mut leaves = NodePtrGuard::new();
                for i in 0..=max_partial_key {
                    leaves.manage(Leaf::new(i as usize, i as usize));
                }
                let mut inner = <$T>::from(Header::from(CompressedPath::default()));
                for i in (0..=max_partial_key) {
                    inner.add(i, leaves[i as usize].into());
                    let max_child = inner.max();
                    assert_eq!(max_child, (i, leaves[i as usize].into()));
                }
            }
        };
    }

    macro_rules! test_inner_empty_min {
        ($name:ident,$T:ty) => {
            #[should_panic = "node is empty"]
            #[test]
            fn $name() {
                let inner = <$T>::from(Header::from(CompressedPath::default()));
                inner.min();
            }
        };
    }

    macro_rules! test_inner_empty_max {
        ($name:ident,$T:ty) => {
            #[should_panic = "node is empty"]
            #[test]
            fn $name() {
                let inner = <$T>::from(Header::from(CompressedPath::default()));
                inner.max();
            }
        };
    }

    macro_rules! test_read_full_prefix {
        ($name:ident,$T:ty) => {
            #[test]
            fn $name() {
                {
                    let inner = <$T>::from(Header::<3>::from(CompressedPath::new(b"abc", 3)));
                    let (key, leaf) = inner.read_full_prefix(0);
                    assert!(leaf.is_none());
                    assert_eq!(&*key, b"abc".as_slice());
                }
                {
                    let mut leaves = NodePtrGuard::<_, _, 3>::new();
                    let min_leaf = leaves.manage(Leaf::new(b"abcdef".to_vec(), 0));

                    let mut inner = <$T>::from(Header::<3>::from(CompressedPath::new(b"abc", 5)));
                    inner.add(b'f', min_leaf.into());

                    let (key, leaf) = inner.read_full_prefix(0);
                    assert_eq!(leaf.expect("read from leaf"), min_leaf);
                    assert_eq!(&*key, b"abcde".as_slice());
                }
            }
        };
    }
    macro_rules! test_match_full_prefix {
        ($name:ident,$T:ty) => {
            #[test]
            fn $name() {
                {
                    let inner = <$T>::from(Header::<3>::from(CompressedPath::new(b"abc", 3)));

                    let result = inner.match_full_prefix(SearchKey::new(b"abcdef"), 0);
                    assert_eq!(result.expect("matching prefix"), 3);

                    let result = inner.match_full_prefix(SearchKey::new(b"ab"), 0);
                    let error = result.unwrap_err();
                    assert_eq!(error.prefix_len, 2);
                    assert_eq!(error.leaf, None);
                }
                {
                    let mut leaves = NodePtrGuard::<_, _, 3>::new();
                    let leaf = leaves.manage(Leaf::new(b"abcdef".to_vec(), 0));

                    let mut inner = <$T>::from(Header::<3>::from(CompressedPath::new(b"abc", 5)));
                    inner.add(b'f', leaf.as_opaque());

                    let result = inner.match_full_prefix(SearchKey::new(b"abcde"), 0);
                    assert_eq!(result.expect("matching prefix"), 5);

                    let result = inner.match_full_prefix(SearchKey::new(b"ab"), 0);
                    let error = result.unwrap_err();
                    assert_eq!(error.prefix_len, 2);
                    assert_eq!(error.leaf.expect("read from leaf"), leaf);

                    let result = inner.match_full_prefix(SearchKey::new(b"abcd"), 0);
                    let error = result.unwrap_err();
                    assert_eq!(error.prefix_len, 4);
                    assert_eq!(error.leaf.expect("read from leaf"), leaf);
                }
            }
        };
    }

    test_inner_grow!(inner4_grow, InnerSorted<usize, usize, 10, 4>, 3, 15);
    test_inner_grow!(inner16_grow, InnerSorted<usize, usize, 10, 16>, 15, 47);
    test_inner_grow!(inner48_grow, Inner48<usize, usize, 10>, 47, 255);

    test_inner_shrink!(inner16_shrink, InnerSorted<usize, usize, 10, 16>, 3);
    test_inner_shrink!(inner48_shrink, Inner48<usize, usize, 10>, 15);
    test_inner_shrink!(inner256_shrink, Inner256<usize, usize, 10 >, 47);

    test_inner_iter!(inner4_iter, InnerSorted<usize, usize, 10, 4>, 3);
    test_inner_iter!(inner16_iter, InnerSorted<usize, usize, 10, 16>, 15);
    test_inner_iter!(inner48_iter, Inner48<usize, usize, 10>, 47);
    test_inner_iter!(inner256_iter, Inner256<usize, usize, 10 >, 255);

    test_inner_add_and_get!(inner4_add_and_get, InnerSorted<usize, usize, 10, 4>, 3);
    test_inner_add_and_get!(inner16_add_and_get, InnerSorted<usize, usize, 10, 16>, 15);
    test_inner_add_and_get!(inner48_add_and_get, Inner48<usize, usize, 10>, 47);
    test_inner_add_and_get!(inner256_add_and_get, Inner256<usize, usize, 10>, 255);

    test_inner_add_and_del!(inner4_add_and_del, InnerSorted<usize, usize, 10, 4>, 3);
    test_inner_add_and_del!(inner16_add_and_del, InnerSorted<usize, usize, 10, 16>, 15);
    test_inner_add_and_del!(inner48_add_and_del, Inner48<usize, usize, 10>, 47);
    test_inner_add_and_del!(inner256_add_and_del, Inner256<usize, usize, 10>, 255);

    test_inner_add_existing!(inner4_add_existing, InnerSorted<usize, usize, 10, 4>, 3);
    test_inner_add_existing!(inner16_add_existing, InnerSorted<usize, usize, 10, 16>, 15);
    test_inner_add_existing!(inner48_add_existing, Inner48<usize, usize, 10>, 47);
    test_inner_add_existing!(inner256_add_existing, Inner256<usize, usize, 10>, 255);

    test_inner_del_and_get!(inner4_del_and_get, InnerSorted<usize, usize, 10, 4>, 3);
    test_inner_del_and_get!(inner16_del_and_get, InnerSorted<usize, usize, 10, 16>, 15);
    test_inner_del_and_get!(inner48_del_and_get, Inner48<usize, usize, 10>, 47);
    test_inner_del_and_get!(inner256_del_and_get, Inner256<usize, usize, 10>, 255);

    test_inner_min!(inner4_min, InnerSorted<usize, usize, 10, 4>, 3);
    test_inner_min!(inner16_min, InnerSorted<usize, usize, 10, 16>, 15);
    test_inner_min!(inner48_min, Inner48<usize, usize, 10>, 47);
    test_inner_min!(inner256_min, Inner256<usize, usize, 10>, 255);

    test_inner_max!(inner4_max, InnerSorted<usize, usize, 10, 4>, 3);
    test_inner_max!(inner16_max, InnerSorted<usize, usize, 10, 16>, 15);
    test_inner_max!(inner48_max, Inner48<usize, usize, 10>, 47);
    test_inner_max!(inner256_max, Inner256<usize, usize, 10>, 255);

    test_inner_empty_min!(inner4_empty_min, InnerSorted<usize, usize, 10, 4>);
    test_inner_empty_min!(inner16_empty_min, InnerSorted<usize, usize, 10, 16>);
    test_inner_empty_min!(inner48_empty_min, Inner48<usize, usize, 10>);
    test_inner_empty_min!(inner256_empty_min, Inner256<usize, usize, 10>);

    test_inner_empty_max!(inner4_empty_max, InnerSorted<usize, usize, 10, 4>);
    test_inner_empty_max!(inner16_empty_max, InnerSorted<usize, usize, 10, 16>);
    test_inner_empty_max!(inner48_empty_max, Inner48<usize, usize, 10>);
    test_inner_empty_max!(inner256_empty_max, Inner256<usize, usize, 10>);

    test_read_full_prefix!(inner4_read_full_prefix, InnerSorted<Vec<u8>, u64, 3, 4>);
    test_read_full_prefix!(inner16_read_full_prefix, InnerSorted<Vec<u8>, u64, 3, 16>);
    test_read_full_prefix!(inner48_read_full_prefix, Inner48<Vec<u8>, u64, 3>);
    test_read_full_prefix!(inner256_read_full_prefix, Inner256<Vec<u8>, u64, 3>);

    test_match_full_prefix!(inner4_match_full_prefix, InnerSorted<Vec<u8>, u64, 3, 4>);
    test_match_full_prefix!(inner16_match_full_prefix, InnerSorted<Vec<u8>, u64, 3, 16>);
    test_match_full_prefix!(inner48_match_full_prefix, Inner48<Vec<u8>, u64, 3>);
    test_match_full_prefix!(inner256_match_full_prefix, Inner256<Vec<u8>, u64, 3>);
}
