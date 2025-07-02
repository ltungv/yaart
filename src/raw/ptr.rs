use std::{
    alloc::{self, Layout},
    fmt,
    hash::Hash,
    marker::PhantomData,
    ptr::NonNull,
};

use crate::tagged_ptr::TaggedPtr;

use super::{Header, Inner, Inner256, Inner48, InnerSorted, Leaf, Node, NodeType};

#[cfg(test)]
pub use tests::*;

/// A [`TaggedPtr`] to the header of a node in a tree in which the pointer is tagged with the type
/// of the node containing the header.
///
/// Only the pointer to a [`Header`] is stored, making [`OpaqueNodePtr`] opaque over the type of
/// node it's pointing to. Every node type ensures that a [`Header`] comes first in their data
/// representation. As a result, the pointer to the start of a [`Header`] is also a pointer to the
/// start of the node's data. Based on the tags of the [`TaggedPtr`], the pointer can then be
/// casted to the correct type of the node being pointed to.
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
            ConcreteNodePtr::Leaf(pointer) => pointer.as_opaque(),
            ConcreteNodePtr::Inner4(pointer) => pointer.as_opaque(),
            ConcreteNodePtr::Inner16(pointer) => pointer.as_opaque(),
            ConcreteNodePtr::Inner48(pointer) => pointer.as_opaque(),
            ConcreteNodePtr::Inner256(pointer) => pointer.as_opaque(),
        }
    }
}

impl<K, V, const PARTIAL_LEN: usize> From<ConcreteInnerNodePtr<K, V, PARTIAL_LEN>>
    for OpaqueNodePtr<K, V, PARTIAL_LEN>
{
    fn from(node_ptr: ConcreteInnerNodePtr<K, V, PARTIAL_LEN>) -> Self {
        match node_ptr {
            ConcreteInnerNodePtr::Inner4(pointer) => pointer.as_opaque(),
            ConcreteInnerNodePtr::Inner16(pointer) => pointer.as_opaque(),
            ConcreteInnerNodePtr::Inner48(pointer) => pointer.as_opaque(),
            ConcreteInnerNodePtr::Inner256(pointer) => pointer.as_opaque(),
        }
    }
}

impl<T, K, V, const PARTIAL_LEN: usize> From<NodePtr<T>> for OpaqueNodePtr<K, V, PARTIAL_LEN>
where
    T: Node<PARTIAL_LEN>,
{
    fn from(node_ptr: NodePtr<T>) -> Self {
        let mut tagged_ptr = TaggedPtr::from(node_ptr.as_ptr()).cast();
        tagged_ptr.tags(T::TYPE as usize);
        Self(tagged_ptr, PhantomData)
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
        f.debug_struct("OpaqueNodePtr")
            .field("ptr", &self.as_ptr())
            .field("type", &self.as_type())
            .finish()
    }
}

impl<K, V, const PARTIAL_LEN: usize> fmt::Pointer for OpaqueNodePtr<K, V, PARTIAL_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}

impl<K, V, const PARTIAL_LEN: usize> OpaqueNodePtr<K, V, PARTIAL_LEN> {
    /// Gets a normalized pointer from the tagged pointer.
    pub fn as_ptr(self) -> NonNull<Header<PARTIAL_LEN>> {
        self.0.as_ptr()
    }

    /// Gets the node type from the tags of the pointer.
    pub fn as_type(self) -> NodeType {
        // SAFETY: Casting the pointer's tags to being an `u8` and transmuting the result to become
        // a `NodeType` is safe because the tagged pointer within `OpaqueNodePtr` is ensured to
        // contain a tags of type `NodeType`.
        unsafe {
            #[allow(clippy::cast_possible_truncation)]
            std::mem::transmute(self.0.as_tags() as u8)
        }
    }

    /// Gets the [`ConcreteNodePtr`] represented by this opaque pointer.
    pub fn as_concrete(self) -> ConcreteNodePtr<K, V, PARTIAL_LEN> {
        self.into()
    }
}

/// An enumeration of different types of node pointer.
pub enum ConcreteNodePtr<K, V, const PARTIAL_LEN: usize> {
    Leaf(NodePtr<Leaf<K, V>>),
    Inner4(NodePtr<InnerSorted<K, V, PARTIAL_LEN, 4>>),
    Inner16(NodePtr<InnerSorted<K, V, PARTIAL_LEN, 16>>),
    Inner48(NodePtr<Inner48<K, V, PARTIAL_LEN>>),
    Inner256(NodePtr<Inner256<K, V, PARTIAL_LEN>>),
}

impl<K, V, const PARTIAL_LEN: usize> Copy for ConcreteNodePtr<K, V, PARTIAL_LEN> {}
impl<K, V, const PARTIAL_LEN: usize> Clone for ConcreteNodePtr<K, V, PARTIAL_LEN> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V, const PARTIAL_LEN: usize> From<OpaqueNodePtr<K, V, PARTIAL_LEN>>
    for ConcreteNodePtr<K, V, PARTIAL_LEN>
{
    fn from(opaque_ptr: OpaqueNodePtr<K, V, PARTIAL_LEN>) -> Self {
        match opaque_ptr.as_type() {
            NodeType::Leaf => Self::Leaf(opaque_ptr.as_ptr().cast().into()),
            NodeType::Inner4 => Self::Inner4(opaque_ptr.as_ptr().cast().into()),
            NodeType::Inner16 => Self::Inner16(opaque_ptr.as_ptr().cast().into()),
            NodeType::Inner48 => Self::Inner48(opaque_ptr.as_ptr().cast().into()),
            NodeType::Inner256 => Self::Inner256(opaque_ptr.as_ptr().cast().into()),
        }
    }
}

impl<K, V, const PARTIAL_LEN: usize> From<ConcreteInnerNodePtr<K, V, PARTIAL_LEN>>
    for ConcreteNodePtr<K, V, PARTIAL_LEN>
{
    fn from(pointer: ConcreteInnerNodePtr<K, V, PARTIAL_LEN>) -> Self {
        match pointer {
            ConcreteInnerNodePtr::Inner4(node_ptr) => Self::Inner4(node_ptr),
            ConcreteInnerNodePtr::Inner16(node_ptr) => Self::Inner16(node_ptr),
            ConcreteInnerNodePtr::Inner48(node_ptr) => Self::Inner48(node_ptr),
            ConcreteInnerNodePtr::Inner256(node_ptr) => Self::Inner256(node_ptr),
        }
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

impl<K, V, const PARTIAL_LEN: usize> Hash for ConcreteNodePtr<K, V, PARTIAL_LEN> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::Leaf(node_ptr) => node_ptr.0.hash(state),
            Self::Inner4(node_ptr) => node_ptr.0.hash(state),
            Self::Inner16(node_ptr) => node_ptr.0.hash(state),
            Self::Inner48(node_ptr) => node_ptr.0.hash(state),
            Self::Inner256(node_ptr) => node_ptr.0.hash(state),
        }
    }
}

impl<K, V, const PARTIAL_LEN: usize> Eq for ConcreteNodePtr<K, V, PARTIAL_LEN> {}
impl<K, V, const PARTIAL_LEN: usize> PartialEq for ConcreteNodePtr<K, V, PARTIAL_LEN> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Leaf(lhs_ptr), Self::Leaf(rhs_ptr)) => lhs_ptr.0 == rhs_ptr.0,
            (Self::Inner4(lhs_ptr), Self::Inner4(rhs_ptr)) => lhs_ptr.0 == rhs_ptr.0,
            (Self::Inner16(lhs_ptr), Self::Inner16(rhs_ptr)) => lhs_ptr.0 == rhs_ptr.0,
            (Self::Inner48(lhs_ptr), Self::Inner48(rhs_ptr)) => lhs_ptr.0 == rhs_ptr.0,
            (Self::Inner256(lhs_ptr), Self::Inner256(rhs_ptr)) => lhs_ptr.0 == rhs_ptr.0,
            _ => false,
        }
    }
}

impl<K, V, const PARTIAL_LEN: usize> fmt::Debug for ConcreteNodePtr<K, V, PARTIAL_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Leaf(node_ptr) => f
                .debug_tuple("ConcreteNodePtr::Leaf")
                .field(node_ptr)
                .finish(),
            Self::Inner4(node_ptr) => f
                .debug_tuple("ConcreteNodePtr::Inner4")
                .field(node_ptr)
                .finish(),
            Self::Inner16(node_ptr) => f
                .debug_tuple("ConcreteNodePtr::Inner16")
                .field(node_ptr)
                .finish(),
            Self::Inner48(node_ptr) => f
                .debug_tuple("ConcreteNodePtr::Inner48")
                .field(node_ptr)
                .finish(),
            Self::Inner256(node_ptr) => f
                .debug_tuple("ConcreteNodePtr::Inner256")
                .field(node_ptr)
                .finish(),
        }
    }
}

impl<K, V, const PARTIAL_LEN: usize> fmt::Pointer for ConcreteNodePtr<K, V, PARTIAL_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Leaf(node_ptr) => fmt::Pointer::fmt(node_ptr, f),
            Self::Inner4(node_ptr) => fmt::Pointer::fmt(node_ptr, f),
            Self::Inner16(node_ptr) => fmt::Pointer::fmt(node_ptr, f),
            Self::Inner48(node_ptr) => fmt::Pointer::fmt(node_ptr, f),
            Self::Inner256(node_ptr) => fmt::Pointer::fmt(node_ptr, f),
        }
    }
}

/// An enumeration of different types of node pointer.
pub enum ConcreteInnerNodePtr<K, V, const PARTIAL_LEN: usize> {
    Inner4(NodePtr<InnerSorted<K, V, PARTIAL_LEN, 4>>),
    Inner16(NodePtr<InnerSorted<K, V, PARTIAL_LEN, 16>>),
    Inner48(NodePtr<Inner48<K, V, PARTIAL_LEN>>),
    Inner256(NodePtr<Inner256<K, V, PARTIAL_LEN>>),
}

impl<K, V, const PARTIAL_LEN: usize> Copy for ConcreteInnerNodePtr<K, V, PARTIAL_LEN> {}
impl<K, V, const PARTIAL_LEN: usize> Clone for ConcreteInnerNodePtr<K, V, PARTIAL_LEN> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, K, V, const PARTIAL_LEN: usize> From<NodePtr<T>> for ConcreteInnerNodePtr<K, V, PARTIAL_LEN>
where
    T: Inner<PARTIAL_LEN>,
{
    fn from(pointer: NodePtr<T>) -> Self {
        match T::TYPE {
            NodeType::Leaf => unreachable!("invalid inner node type"),
            NodeType::Inner4 => Self::Inner4(pointer.as_ptr().cast().into()),
            NodeType::Inner16 => Self::Inner16(pointer.as_ptr().cast().into()),
            NodeType::Inner48 => Self::Inner48(pointer.as_ptr().cast().into()),
            NodeType::Inner256 => Self::Inner256(pointer.as_ptr().cast().into()),
        }
    }
}

impl<K, V, const PARTIAL_LEN: usize> Hash for ConcreteInnerNodePtr<K, V, PARTIAL_LEN> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            Self::Inner4(node_ptr) => node_ptr.0.hash(state),
            Self::Inner16(node_ptr) => node_ptr.0.hash(state),
            Self::Inner48(node_ptr) => node_ptr.0.hash(state),
            Self::Inner256(node_ptr) => node_ptr.0.hash(state),
        }
    }
}

impl<K, V, const PARTIAL_LEN: usize> Eq for ConcreteInnerNodePtr<K, V, PARTIAL_LEN> {}
impl<K, V, const PARTIAL_LEN: usize> PartialEq for ConcreteInnerNodePtr<K, V, PARTIAL_LEN> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Inner4(lhs_ptr), Self::Inner4(rhs_ptr)) => lhs_ptr.0 == rhs_ptr.0,
            (Self::Inner16(lhs_ptr), Self::Inner16(rhs_ptr)) => lhs_ptr.0 == rhs_ptr.0,
            (Self::Inner48(lhs_ptr), Self::Inner48(rhs_ptr)) => lhs_ptr.0 == rhs_ptr.0,
            (Self::Inner256(lhs_ptr), Self::Inner256(rhs_ptr)) => lhs_ptr.0 == rhs_ptr.0,
            _ => false,
        }
    }
}

impl<K, V, const PARTIAL_LEN: usize> fmt::Debug for ConcreteInnerNodePtr<K, V, PARTIAL_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Inner4(node_ptr) => f
                .debug_tuple("ConcreteInnerNodePtr::Inner4")
                .field(node_ptr)
                .finish(),
            Self::Inner16(node_ptr) => f
                .debug_tuple("ConcreteInnerNodePtr::Inner16")
                .field(node_ptr)
                .finish(),
            Self::Inner48(node_ptr) => f
                .debug_tuple("ConcreteInnerNodePtr::Inner48")
                .field(node_ptr)
                .finish(),
            Self::Inner256(node_ptr) => f
                .debug_tuple("ConcreteInnerNodePtr::Inner256")
                .field(node_ptr)
                .finish(),
        }
    }
}

impl<K, V, const PARTIAL_LEN: usize> fmt::Pointer for ConcreteInnerNodePtr<K, V, PARTIAL_LEN> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Inner4(node_ptr) => fmt::Pointer::fmt(node_ptr, f),
            Self::Inner16(node_ptr) => fmt::Pointer::fmt(node_ptr, f),
            Self::Inner48(node_ptr) => fmt::Pointer::fmt(node_ptr, f),
            Self::Inner256(node_ptr) => fmt::Pointer::fmt(node_ptr, f),
        }
    }
}

impl<K, V, const PARTIAL_LEN: usize> ConcreteInnerNodePtr<K, V, PARTIAL_LEN> {
    /// Gets the [`OpaqueNodePtr`] represented by this opaque pointer.
    pub fn as_opaque(self) -> OpaqueNodePtr<K, V, PARTIAL_LEN> {
        self.into()
    }

    pub const unsafe fn header<'a>(self) -> &'a Header<PARTIAL_LEN> {
        let header_ptr = match self {
            Self::Inner4(node_ptr) => node_ptr.as_ptr().cast(),
            Self::Inner16(node_ptr) => node_ptr.as_ptr().cast(),
            Self::Inner48(node_ptr) => node_ptr.as_ptr().cast(),
            Self::Inner256(node_ptr) => node_ptr.as_ptr().cast(),
        };
        unsafe { header_ptr.as_ref() }
    }

    pub const unsafe fn header_mut<'a>(self) -> &'a mut Header<PARTIAL_LEN> {
        let mut header_ptr = match self {
            Self::Inner4(node_ptr) => node_ptr.as_ptr().cast(),
            Self::Inner16(node_ptr) => node_ptr.as_ptr().cast(),
            Self::Inner48(node_ptr) => node_ptr.as_ptr().cast(),
            Self::Inner256(node_ptr) => node_ptr.as_ptr().cast(),
        };
        unsafe { header_ptr.as_mut() }
    }
}

/// A pointer to a node in a tree.
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

impl<T> Hash for NodePtr<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<T> Eq for NodePtr<T> {}

impl<T> PartialEq for NodePtr<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> fmt::Debug for NodePtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("NodePtr").field(&self.0).finish()
    }
}

impl<T> fmt::Pointer for NodePtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}

impl<T> NodePtr<T> {
    pub const fn as_ptr(self) -> NonNull<T> {
        self.0
    }
}

impl<T> NodePtr<T> {
    const LAYOUT: Layout = Layout::new::<T>();

    /// Allocates a new node and returns a pointer to its data.
    pub fn alloc(node: T) -> Self {
        let unchecked_ptr = unsafe { alloc::alloc(Self::LAYOUT) };
        let Some(ptr) = NonNull::new(unchecked_ptr.cast::<T>()) else {
            std::alloc::handle_alloc_error(Self::LAYOUT);
        };
        unsafe {
            ptr.write(node);
        }
        Self(ptr)
    }

    /// Deallocates the node data located at the given pointer.
    pub unsafe fn dealloc(self) {
        let node_ptr = self.0.as_ptr();
        unsafe {
            node_ptr.drop_in_place();
            alloc::dealloc(node_ptr.cast(), Self::LAYOUT);
        }
    }

    /// Returns a shared reference to the data behind this pointer.
    pub const unsafe fn as_ref<'a>(self) -> &'a T {
        unsafe { self.0.as_ref() }
    }

    /// Returns an owned reference to the data behind this pointer.
    pub const unsafe fn as_mut<'a>(mut self) -> &'a mut T {
        unsafe { self.0.as_mut() }
    }

    pub fn as_opaque<const PARTIAL_LEN: usize>(self) -> OpaqueNodePtr<T::Key, T::Value, PARTIAL_LEN>
    where
        T: Node<PARTIAL_LEN>,
    {
        self.into()
    }
}

#[cfg(test)]
pub mod tests {
    use std::collections::HashSet;

    use crate::raw::Node;

    use super::{NodePtr, OpaqueNodePtr};

    /// A container for node pointers that deallocates all contained pointers when going out-of-scope.
    #[cfg(test)]
    pub struct NodePtrGuard<K, V, const PARTIAL_LEN: usize> {
        pub ptrs: Vec<OpaqueNodePtr<K, V, PARTIAL_LEN>>,
        uniqueness: HashSet<OpaqueNodePtr<K, V, PARTIAL_LEN>>,
    }

    #[cfg(test)]
    impl<K, V, const PARTIAL_LEN: usize> Drop for NodePtrGuard<K, V, PARTIAL_LEN> {
        fn drop(&mut self) {
            for ptr in self.ptrs.drain(..) {
                unsafe {
                    match ptr.as_concrete() {
                        super::ConcreteNodePtr::Leaf(node_ptr) => NodePtr::dealloc(node_ptr),
                        super::ConcreteNodePtr::Inner4(node_ptr) => NodePtr::dealloc(node_ptr),
                        super::ConcreteNodePtr::Inner16(node_ptr) => NodePtr::dealloc(node_ptr),
                        super::ConcreteNodePtr::Inner48(node_ptr) => NodePtr::dealloc(node_ptr),
                        super::ConcreteNodePtr::Inner256(node_ptr) => NodePtr::dealloc(node_ptr),
                    }
                }
            }
        }
    }

    #[cfg(test)]
    impl<K, V, const PARTIAL_LEN: usize> std::ops::Index<usize> for NodePtrGuard<K, V, PARTIAL_LEN> {
        type Output = OpaqueNodePtr<K, V, PARTIAL_LEN>;

        fn index(&self, index: usize) -> &Self::Output {
            &self.ptrs[index]
        }
    }

    #[cfg(test)]
    impl<K, V, const PARTIAL_LEN: usize> NodePtrGuard<K, V, PARTIAL_LEN> {
        pub fn new() -> Self {
            Self {
                ptrs: Vec::new(),
                uniqueness: HashSet::new(),
            }
        }

        pub fn manage<T>(&mut self, node: T) -> NodePtr<T>
        where
            T: Node<PARTIAL_LEN, Key = K, Value = V>,
        {
            let pointer = NodePtr::alloc(node);
            let opaqe_ptr = pointer.as_opaque();
            if self.uniqueness.insert(opaqe_ptr) {
                self.ptrs.push(opaqe_ptr);
            }
            pointer
        }
    }
}
