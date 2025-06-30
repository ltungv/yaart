use crate::v2::Sealed;

use super::{Node, NodeType};

pub struct Leaf<K, V> {
    pub key: K,
    pub value: V,
}

impl<K, V> From<(K, V)> for Leaf<K, V> {
    fn from((key, value): (K, V)) -> Self {
        Self::new(key, value)
    }
}

impl<K, V> Sealed for Leaf<K, V> {}

impl<K, V, const PARTIAL_LEN: usize> Node<PARTIAL_LEN> for Leaf<K, V> {
    const TYPE: NodeType = NodeType::Leaf;
    type Key = K;
    type Value = V;
}

impl<K, V> Leaf<K, V> {
    pub fn new(key: K, value: V) -> Self {
        Self { key, value }
    }
}
