mod ptr;
mod fmt;
mod insert;
mod search;

use crate::raw::NodePtr;

use super::raw::{ConcreteInnerNodePtr, Leaf};

pub use ptr::*;
pub use fmt::*;
pub use insert::*;
pub use search::*;

/// A branch determines the origin of a node in the tree consisting of a pointer to the node's
/// parent and a key partial that locates the node within its parent.
#[derive(Debug, PartialEq, Eq)]
pub struct Branch<K, V, const PARTIAL_LEN: usize> {
    pub ptr: ConcreteInnerNodePtr<K, V, PARTIAL_LEN>,
    pub key: u8,
}

/// An error from matching with a full prefix.
#[derive(Debug, PartialEq, Eq)]
pub struct FullPrefixMismatch<K, V, const PARTIAL_LEN: usize> {
    pub prefix_len: usize,
    pub mismatched: u8,
    pub leaf: Option<NodePtr<Leaf<K, V>>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct PrefixMismatch {
    pub prefix_len: usize,
    pub mismatched: Option<u8>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum PrefixMatch {
    Optimistic(usize),
    Pessimistic(usize),
}
