use std::fmt;

use crate::{BytesRepr, Sealed};

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

impl<K, V> fmt::Debug for Leaf<K, V>
where
    K: BytesRepr,
    V: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Leaf").field("key", &self.key.repr()).field("value", &self.value).finish()
    }
}

impl<K, V> Sealed for Leaf<K, V> {}

impl<K, V, const PARTIAL_LEN: usize> Node<PARTIAL_LEN> for Leaf<K, V> {
    const TYPE: NodeType = NodeType::Leaf;
    type Key = K;
    type Value = V;
}

impl<K, V> Leaf<K, V> {
    pub const fn new(key: K, value: V) -> Self {
        Self { key, value }
    }
}
