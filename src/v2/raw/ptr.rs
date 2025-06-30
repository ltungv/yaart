use std::{
    alloc::{self, Layout},
    fmt,
    hash::Hash,
    marker::PhantomData,
    ptr::NonNull,
};

use crate::v2::tagged_ptr::TaggedPtr;

use super::{Header, Inner, Inner256, Inner48, InnerSorted, Leaf, Node, NodeType};

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
        let mut tagged_ptr = TaggedPtr::from(node_ptr.as_ptr()).cast();
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
        unsafe { std::mem::transmute(self.0.as_tags() as u8) }
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
            ConcreteInnerNodePtr::Inner4(inner_ptr) => Self::Inner4(inner_ptr),
            ConcreteInnerNodePtr::Inner16(inner_ptr) => Self::Inner16(inner_ptr),
            ConcreteInnerNodePtr::Inner48(inner_ptr) => Self::Inner48(inner_ptr),
            ConcreteInnerNodePtr::Inner256(inner_ptr) => Self::Inner256(inner_ptr),
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
            NodeType::Inner4 => Self::Inner4(pointer.as_ptr().cast().into()),
            NodeType::Inner16 => Self::Inner16(pointer.as_ptr().cast().into()),
            NodeType::Inner48 => Self::Inner48(pointer.as_ptr().cast().into()),
            NodeType::Inner256 => Self::Inner256(pointer.as_ptr().cast().into()),
            _ => unreachable!("invalid inner node type"),
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
    fn as_ptr(self) -> NonNull<T> {
        self.0
    }
}

impl<T> NodePtr<T> {
    const LAYOUT: Layout = Layout::new::<T>();

    /// Allocates a new node and returns a pointer to its data.
    pub fn alloc(node: T) -> NodePtr<T> {
        let unchecked_ptr = unsafe { alloc::alloc(Self::LAYOUT) };
        let Some(ptr) = NonNull::new(unchecked_ptr.cast::<T>()) else {
            std::alloc::handle_alloc_error(Self::LAYOUT);
        };
        unsafe {
            ptr.write(node);
        }
        NodePtr(ptr)
    }

    /// Deallocates the node data located at the given pointer.
    pub unsafe fn dealloc(self) {
        unsafe { alloc::dealloc(self.0.as_ptr().cast(), Self::LAYOUT) };
    }

    /// Returns a shared reference to the data behind this pointer.
    pub unsafe fn as_ref<'a>(self) -> &'a T {
        unsafe { self.0.as_ref() }
    }

    /// Returns an owned reference to the data behind this pointer.
    pub unsafe fn as_mut<'a>(mut self) -> &'a mut T {
        unsafe { self.0.as_mut() }
    }
}
