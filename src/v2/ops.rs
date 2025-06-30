mod insert;
mod search;

use crate::v2::raw::NodePtr;

use super::raw::{ConcreteInnerNodePtr, Leaf};

pub use insert::*;
pub use search::*;

/// A branch determines the origin of a node in the tree consisting of a pointer to the node's
/// parent and a key partial that locates the node within its parent.
pub struct Branch<K, V, const PARTIAL_LEN: usize> {
    pub ptr: ConcreteInnerNodePtr<K, V, PARTIAL_LEN>,
    pub key: u8,
}

pub struct FullPrefixMismatch<K, V, const PARTIAL_LEN: usize> {
    pub mismatch: u8,
    pub prefix_len: usize,
    pub leaf: Option<NodePtr<Leaf<K, V>>>,
}
