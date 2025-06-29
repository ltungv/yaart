mod header;
mod inner256;
mod inner48;
mod inner_sorted;
mod leaf;
mod ops;

use std::{
    alloc::{self, Layout},
    error, fmt,
    marker::PhantomData,
    ptr::NonNull,
};

use crate::v2::{tagged_ptr::TaggedPtr, Sealed};

pub use header::*;
pub use inner256::*;
pub use inner48::*;
pub use inner_sorted::*;
pub use leaf::*;

trait Node<const PARTIAL_LEN: usize>: Sealed {
    /// The runtime type of the node.
    const TYPE: NodeType;
    /// The key type carried by the leaf nodes
    type Key;
    /// The value type carried by the leaf nodes
    type Value;
}

trait Inner<const PARTIAL_LEN: usize>: Node<PARTIAL_LEN> {
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
}

#[derive(Debug)]
pub enum NodeTypeError {
    TryFromTags { tags: usize },
}

impl error::Error for NodeTypeError {}

impl fmt::Display for NodeTypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeTypeError::TryFromTags { tags } => {
                write!(f, "tags is invalid ({tags:b})")
            }
        }
    }
}

#[repr(u8)]
pub enum NodeType {
    Leaf = 0,
    Inner4 = 1,
    Inner16 = 2,
    Inner48 = 3,
    Inner256 = 4,
}

impl TryFrom<usize> for NodeType {
    type Error = NodeTypeError;

    fn try_from(tags: usize) -> Result<Self, Self::Error> {
        match tags {
            0 => Ok(Self::Leaf),
            1 => Ok(Self::Inner4),
            2 => Ok(Self::Inner16),
            3 => Ok(Self::Inner48),
            4 => Ok(Self::Inner256),
            _ => Err(NodeTypeError::TryFromTags { tags }),
        }
    }
}

#[repr(transparent)]
pub struct OpaqueNodePtr<K, V, const PARTIAL_LEN: usize>(
    TaggedPtr<Header<PARTIAL_LEN>, 3>,
    PhantomData<(K, V)>,
);

impl<K, V, const PARTIAL_LEN: usize> Copy for OpaqueNodePtr<K, V, PARTIAL_LEN> {}
impl<K, V, const PARTIAL_LEN: usize> Clone for OpaqueNodePtr<K, V, PARTIAL_LEN> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V, const PARTIAL_LEN: usize> From<ConcreteNodePtr<K, V, PARTIAL_LEN>>
    for OpaqueNodePtr<K, V, PARTIAL_LEN>
{
    fn from(node_ptr: ConcreteNodePtr<K, V, PARTIAL_LEN>) -> Self {
        match node_ptr {
            ConcreteNodePtr::Leaf(pointer) => OpaqueNodePtr::from(pointer),
            ConcreteNodePtr::Inner4(pointer) => OpaqueNodePtr::from(pointer),
            ConcreteNodePtr::Inner16(pointer) => OpaqueNodePtr::from(pointer),
            ConcreteNodePtr::Inner48(pointer) => OpaqueNodePtr::from(pointer),
            ConcreteNodePtr::Inner256(pointer) => OpaqueNodePtr::from(pointer),
        }
    }
}

impl<T, K, V, const PARTIAL_LEN: usize> From<NodePtr<T>> for OpaqueNodePtr<K, V, PARTIAL_LEN>
where
    T: Node<PARTIAL_LEN>,
{
    fn from(node_ptr: NodePtr<T>) -> Self {
        let mut tagged_ptr = TaggedPtr::from(node_ptr.as_ptr().cast::<Header<PARTIAL_LEN>>());
        tagged_ptr.tags(T::TYPE as usize);
        OpaqueNodePtr(tagged_ptr, PhantomData)
    }
}

impl<K, V, const PARTIAL_LEN: usize> std::hash::Hash for OpaqueNodePtr<K, V, PARTIAL_LEN> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<K, V, const PARTIAL_LEN: usize> Eq for OpaqueNodePtr<K, V, PARTIAL_LEN> {}
impl<K, V, const PARTIAL_LEN: usize> PartialEq for OpaqueNodePtr<K, V, PARTIAL_LEN> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<K, V, const PARTIAL_LEN: usize> fmt::Debug for OpaqueNodePtr<K, V, PARTIAL_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<K, V, const PARTIAL_LEN: usize> fmt::Pointer for OpaqueNodePtr<K, V, PARTIAL_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<K, V, const PARTIAL_LEN: usize> OpaqueNodePtr<K, V, PARTIAL_LEN> {
    pub fn as_ptr(self) -> TaggedPtr<Header<PARTIAL_LEN>, 3> {
        self.0
    }
}

pub enum ConcreteNodePtr<K, V, const PARTIAL_LEN: usize> {
    Leaf(NodePtr<Leaf<K, V>>),
    Inner4(NodePtr<InnerSorted<K, V, PARTIAL_LEN, 4>>),
    Inner16(NodePtr<InnerSorted<K, V, PARTIAL_LEN, 16>>),
    Inner48(NodePtr<Inner48<K, V, PARTIAL_LEN>>),
    Inner256(NodePtr<Inner256<K, V, PARTIAL_LEN>>),
}

impl<K, V, const PARTIAL_LEN: usize> TryFrom<OpaqueNodePtr<K, V, PARTIAL_LEN>>
    for ConcreteNodePtr<K, V, PARTIAL_LEN>
{
    type Error = NodeTypeError;

    fn try_from(opaque_ptr: OpaqueNodePtr<K, V, PARTIAL_LEN>) -> Result<Self, Self::Error> {
        let tagged_ptr: TaggedPtr<Header<PARTIAL_LEN>, 3> = opaque_ptr.as_ptr();
        NodeType::try_from(tagged_ptr.as_tags()).map(|node_type| match node_type {
            NodeType::Leaf => ConcreteNodePtr::Leaf(tagged_ptr.as_ptr().cast().into()),
            NodeType::Inner4 => ConcreteNodePtr::Inner4(tagged_ptr.as_ptr().cast().into()),
            NodeType::Inner16 => ConcreteNodePtr::Inner16(tagged_ptr.as_ptr().cast().into()),
            NodeType::Inner48 => ConcreteNodePtr::Inner48(tagged_ptr.as_ptr().cast().into()),
            NodeType::Inner256 => ConcreteNodePtr::Inner256(tagged_ptr.as_ptr().cast().into()),
        })
    }
}

impl<T, K, V, const PARTIAL_LEN: usize> From<NodePtr<T>> for ConcreteNodePtr<K, V, PARTIAL_LEN>
where
    T: Node<PARTIAL_LEN>,
{
    fn from(pointer: NodePtr<T>) -> Self {
        match T::TYPE {
            NodeType::Leaf => Self::Leaf(pointer.as_ptr().cast().into()),
            NodeType::Inner4 => Self::Inner4(pointer.as_ptr().cast().into()),
            NodeType::Inner16 => Self::Inner16(pointer.as_ptr().cast().into()),
            NodeType::Inner48 => Self::Inner48(pointer.as_ptr().cast().into()),
            NodeType::Inner256 => Self::Inner256(pointer.as_ptr().cast().into()),
        }
    }
}

#[repr(transparent)]
pub struct NodePtr<T>(NonNull<T>);

impl<T> Copy for NodePtr<T> {}
impl<T> Clone for NodePtr<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> From<NonNull<T>> for NodePtr<T> {
    fn from(pointer: NonNull<T>) -> Self {
        Self(pointer)
    }
}

impl<T> NodePtr<T> {
    fn as_ptr(self) -> NonNull<T> {
        self.0
    }
}

impl<T> NodePtr<T> {
    fn layout() -> Layout {
        Layout::new::<T>()
    }

    pub fn alloc(node: T) -> NodePtr<T> {
        let layout = Self::layout();
        let unchecked_ptr = unsafe { alloc::alloc(layout) };
        let Some(ptr) = NonNull::new(unchecked_ptr.cast::<T>()) else {
            std::alloc::handle_alloc_error(layout);
        };
        unsafe {
            ptr.write(node);
        }
        NodePtr(ptr)
    }

    unsafe fn dealloc(self) {
        unsafe { alloc::dealloc(self.0.as_ptr().cast(), Self::layout()) };
    }

    unsafe fn as_ref(&self) -> &T {
        unsafe { self.0.as_ref() }
    }

    unsafe fn as_mut(&mut self) -> &mut T {
        unsafe { self.0.as_mut() }
    }
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
            for i in (0..=max_key_partial) {
                inner.add(i, leaves.ptrs[i as usize].into());
                let min_child = inner.max();
                assert_eq!(min_child, (i, leaves.ptrs[i as usize].into()));
            }
        }
        test::<InnerSorted<usize, usize, 10, 4>, 10>(3);
        test::<InnerSorted<usize, usize, 10, 16>, 10>(15);
    }
}
