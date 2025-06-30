mod header;
mod inner256;
mod inner48;
mod inner_sorted;
mod leaf;
mod ptr;

use crate::v2::Sealed;

pub use header::*;
pub use inner256::*;
pub use inner48::*;
pub use inner_sorted::*;
pub use leaf::*;
pub use ptr::*;

use super::{
    key::BytesRepr,
    ops::{FullPrefixMismatch, Search},
    search_key::SearchKey,
};

/// Every type of node in a tree implements this trait.
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

    /// Grows this node into the next larger type, copying over children and prefix information.
    fn grow(&self) -> Self::GrownNode;

    /// Shrinks this node into the next smaller class, copying over children and prefix
    /// information.
    fn shrink(&self) -> Self::ShrunkNode;

    /// Returns the header of this node.
    fn header(&self) -> &Header<PARTIAL_LEN>;

    /// Adds a child pointer with a key partial to this node.
    fn add(
        &mut self,
        key_partial: u8,
        child_ptr: OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>,
    );

    /// Deletes a child pointer at the key partial from this node.
    fn del(
        &mut self,
        key_partial: u8,
    ) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>>;

    /// Gets a child pointer that corresponds to the given key partial.
    fn get(&self, key_partial: u8) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>>;

    /// Returns the minimum child pointer of this node and it's key
    fn min(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>);

    /// Returns the maximum child pointer of this inner and it's key
    fn max(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>);

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
            (SearchKey::new(header.path.as_ref()), None)
        } else {
            // Find the minimum leaf which is guaranteed to have the full prefix of this node.
            let leaf_ptr = unsafe { Search::minimum(self.min().1) };
            let leaf = unsafe { leaf_ptr.as_ref() };
            let key = SearchKey::new(leaf.key.repr());
            let prefix = key.range(current_depth, header.path.prefix_len());
            (prefix, Some(leaf_ptr))
        }
    }

    /// Compares the compressed path of a node with the key and returns the number of equal bytes.
    ///
    /// The full prefix for this node will be read, even if a descendant leaf node needs to be
    /// searched to find implicit bytes.
    #[inline]
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
            Err(FullPrefixMismatch {
                mismatch: prefix[prefix_len],
                prefix_len,
                leaf,
            })
        } else {
            Ok(prefix_len)
        }
    }
}

/// An enum of all node types.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum NodeType {
    /// The type of a leaf node.
    Leaf = 0,
    /// The type of an inner node that can hold a maximum of 4 children.
    Inner4 = 1,
    /// The type of an inner node that can hold a maximum of 16 children.
    Inner16 = 2,
    /// The type of an inner node that can hold a maximum of 48 children.
    Inner48 = 3,
    /// The type of an inner node that can hold a maximum of 256 children.
    Inner256 = 4,
}

#[cfg(test)]
mod tests {
    use crate::v2::{
        compressed_path::CompressedPath,
        raw::{Inner256, Inner48},
    };

    use super::{Header, Inner, InnerSorted, Leaf, NodePtr};

    struct TestLeaves {
        ptrs: Box<[NodePtr<Leaf<usize, usize>>]>,
    }

    impl Drop for TestLeaves {
        fn drop(&mut self) {
            for &ptr in &self.ptrs {
                unsafe {
                    NodePtr::dealloc(ptr);
                }
            }
        }
    }

    impl TestLeaves {
        fn new(count: usize) -> Self {
            Self {
                ptrs: (0..count)
                    .map(|i| NodePtr::alloc(Leaf::new(i, i)))
                    .collect(),
            }
        }
    }

    #[test]
    fn inner_add_and_get() {
        fn test<T, const PARTIAL_LEN: usize>(max_key_partial: u8)
        where
            T: Inner<PARTIAL_LEN> + From<Header<PARTIAL_LEN>>,
        {
            let leaves = TestLeaves::new(max_key_partial as usize + 1);
            let mut inner = T::from(Header::from(CompressedPath::default()));
            for i in 0..=max_key_partial {
                inner.add(i, leaves.ptrs[i as usize].into());
                assert_eq!(inner.header().children, i as u16 + 1)
            }
            for i in 0..=max_key_partial {
                assert_eq!(inner.get(i), Some(leaves.ptrs[i as usize].into()))
            }
        }
        test::<InnerSorted<usize, usize, 10, 4>, 10>(3);
        test::<InnerSorted<usize, usize, 10, 16>, 10>(15);
        test::<Inner48<usize, usize, 10>, 10>(47);
        test::<Inner256<usize, usize, 10>, 10>(255);
    }

    #[test]
    fn inner_add_and_del() {
        fn test<T, const PARTIAL_LEN: usize>(max_key_partial: u8)
        where
            T: Inner<PARTIAL_LEN> + From<Header<PARTIAL_LEN>>,
        {
            let mut inner = T::from(Header::from(CompressedPath::default()));
            {
                let leaves = TestLeaves::new(max_key_partial as usize + 1);
                for i in 0..=max_key_partial {
                    inner.add(i, leaves.ptrs[i as usize].into());
                    assert_eq!(inner.header().children, i as u16 + 1)
                }
                for i in 0..=max_key_partial {
                    assert_eq!(inner.del(i), Some(leaves.ptrs[i as usize].into()));
                    assert_eq!(inner.header().children, u16::from(max_key_partial - i));
                }
            }
            {
                let leaves = TestLeaves::new(max_key_partial as usize + 1);
                for i in 0..=max_key_partial {
                    inner.add(i, leaves.ptrs[i as usize].into());
                    assert_eq!(inner.header().children, i as u16 + 1)
                }
                for i in 0..=max_key_partial {
                    assert_eq!(inner.get(i), Some(leaves.ptrs[i as usize].into()))
                }
            }
        }
        test::<InnerSorted<usize, usize, 10, 4>, 10>(3);
        test::<InnerSorted<usize, usize, 10, 16>, 10>(15);
        test::<Inner48<usize, usize, 10>, 10>(47);
        test::<Inner256<usize, usize, 10>, 10>(255);
    }

    #[test]
    fn inner_add_existing() {
        fn test<T, const PARTIAL_LEN: usize>(max_key_partial: u8)
        where
            T: Inner<PARTIAL_LEN> + From<Header<PARTIAL_LEN>>,
        {
            let mut inner = T::from(Header::from(CompressedPath::default()));
            {
                let leaves = TestLeaves::new(max_key_partial as usize + 1);
                for i in 0..=max_key_partial {
                    inner.add(i, leaves.ptrs[i as usize].into());
                    assert_eq!(inner.header().children, i as u16 + 1)
                }
                for i in 0..=max_key_partial {
                    assert_eq!(inner.get(i), Some(leaves.ptrs[i as usize].into()))
                }
            }
            {
                let leaves = TestLeaves::new(max_key_partial as usize + 1);
                for i in 0..=max_key_partial {
                    inner.add(i, leaves.ptrs[i as usize].into());
                    assert_eq!(inner.header().children, u16::from(max_key_partial) + 1)
                }
                for i in 0..=max_key_partial {
                    assert_eq!(inner.get(i), Some(leaves.ptrs[i as usize].into()))
                }
            }
        }
        test::<InnerSorted<usize, usize, 10, 4>, 10>(3);
        test::<InnerSorted<usize, usize, 10, 16>, 10>(15);
        test::<Inner48<usize, usize, 10>, 10>(47);
        test::<Inner256<usize, usize, 10>, 10>(255);
    }

    #[test]
    fn inner_del_and_get() {
        fn test<T, const PARTIAL_LEN: usize>(max_key_partial: u8)
        where
            T: Inner<PARTIAL_LEN> + From<Header<PARTIAL_LEN>>,
        {
            let leaves = TestLeaves::new(max_key_partial as usize + 1);
            let mut inner = T::from(Header::from(CompressedPath::default()));
            for i in 0..=max_key_partial {
                assert!(inner.del(i).is_none());
            }
            for i in 0..=max_key_partial {
                inner.add(i, leaves.ptrs[i as usize].into());
            }
            for i in 0..=max_key_partial {
                let child = inner.del(i);
                assert_eq!(child, Some(leaves.ptrs[i as usize].into()));
                let child = inner.get(i);
                assert!(child.is_none());
            }
            assert_eq!(inner.header().children, 0);
        }
        test::<InnerSorted<usize, usize, 10, 4>, 10>(3);
        test::<InnerSorted<usize, usize, 10, 16>, 10>(15);
        test::<Inner48<usize, usize, 10>, 10>(47);
        test::<Inner256<usize, usize, 10>, 10>(255);
    }

    #[test]
    fn inner_min() {
        fn test<T, const PARTIAL_LEN: usize>(max_key_partial: u8)
        where
            T: Inner<PARTIAL_LEN> + From<Header<PARTIAL_LEN>>,
        {
            let leaves = TestLeaves::new(max_key_partial as usize + 1);
            let mut inner = T::from(Header::from(CompressedPath::default()));
            for i in (0..=max_key_partial).rev() {
                inner.add(i, leaves.ptrs[i as usize].into());
                let min_child = inner.min();
                assert_eq!(min_child, (i, leaves.ptrs[i as usize].into()));
            }
        }
        test::<InnerSorted<usize, usize, 10, 4>, 10>(3);
        test::<InnerSorted<usize, usize, 10, 16>, 10>(15);
        test::<Inner48<usize, usize, 10>, 10>(47);
        test::<Inner256<usize, usize, 10>, 10>(255);
    }

    #[test]
    fn inner_max() {
        fn test<T, const PARTIAL_LEN: usize>(max_key_partial: u8)
        where
            T: Inner<PARTIAL_LEN> + From<Header<PARTIAL_LEN>>,
        {
            let leaves = TestLeaves::new(max_key_partial as usize + 1);
            let mut inner = T::from(Header::from(CompressedPath::default()));
            for i in 0..=max_key_partial {
                inner.add(i, leaves.ptrs[i as usize].into());
                let min_child = inner.max();
                assert_eq!(min_child, (i, leaves.ptrs[i as usize].into()));
            }
        }
        test::<InnerSorted<usize, usize, 10, 4>, 10>(3);
        test::<InnerSorted<usize, usize, 10, 16>, 10>(15);
        test::<Inner48<usize, usize, 10>, 10>(47);
        test::<Inner256<usize, usize, 10>, 10>(255);
    }
}
