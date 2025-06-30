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
    key::AsSearchKey,
    ops::{FullPrefixMismatch, Ops},
    search_key::SearchKey,
};

pub trait Node<const PARTIAL_LEN: usize>: Sealed {
    /// The runtime type of the node.
    const TYPE: NodeType;
    /// The key type carried by the leaf nodes
    type Key;
    /// The value type carried by the leaf nodes
    type Value;
}

pub trait Inner<const PARTIAL_LEN: usize>: Node<PARTIAL_LEN> {
    type GrownNode: Inner<PARTIAL_LEN, Key = Self::Key, Value = Self::Value>;
    type ShrunkNode: Inner<PARTIAL_LEN, Key = Self::Key, Value = Self::Value>;

    fn grow(&self) -> Self::GrownNode;

    fn shrink(&self) -> Self::ShrunkNode;

    fn header(&self) -> &Header<PARTIAL_LEN>;

    fn add(
        &mut self,
        key_partial: u8,
        child_ptr: OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>,
    );

    fn del(
        &mut self,
        key_partial: u8,
    ) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>>;

    fn get(&self, key_partial: u8) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>>;

    fn min(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>);

    fn max(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>);

    fn read_full_prefix(
        &self,
        current_depth: usize,
    ) -> (SearchKey<'_>, Option<NodePtr<Leaf<Self::Key, Self::Value>>>)
    where
        Self::Key: AsSearchKey,
    {
        let header = self.header();
        let len = header.path.prefix_len();
        // The remaining common prefix is contained within the compressed path.
        if len <= PARTIAL_LEN {
            return (SearchKey::new(header.path.as_ref()), None);
        }
        // Find the minimum leaf which is guaranteed to have the full prefix of this inner node.
        let leaf_ptr = unsafe { Ops::<Self::Key, Self::Value, PARTIAL_LEN>::minimum(self.min().1) };
        let leaf = unsafe { leaf_ptr.as_ref() };
        let prefix = leaf.key.key().range(current_depth, len);
        (prefix, Some(leaf_ptr))
    }

    #[inline]
    fn match_full_prefix(
        &self,
        key: SearchKey<'_>,
        current_depth: usize,
    ) -> Result<usize, FullPrefixMismatch<Self::Key, Self::Value, PARTIAL_LEN>>
    where
        Self::Key: AsSearchKey,
    {
        let (prefix, leaf) = self.read_full_prefix(current_depth);
        let prefix_len = prefix.common_prefix_len(key.shift(current_depth));
        if prefix_len < prefix.len() {
            return Err(FullPrefixMismatch {
                mismatch: prefix[prefix_len],
                prefix_len,
                leaf,
            });
        }
        Ok(prefix_len)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum NodeType {
    Leaf = 0,
    Inner4 = 1,
    Inner16 = 2,
    Inner48 = 3,
    Inner256 = 4,
}

#[cfg(test)]
mod tests {
    use crate::v2::compressed_path::CompressedPath;

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
    }
}
