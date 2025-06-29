use crate::v2::Sealed;

use super::{Header, Inner, Inner48, Node, NodeType, OpaqueNodePtr};

#[repr(C)]
pub struct Inner256<K, V, const PARTIAL_LEN: usize> {
    header: Header<PARTIAL_LEN>,
    ptrs: [Option<OpaqueNodePtr<K, V, PARTIAL_LEN>>; 256],
}

impl<K, V, const PARTIAL_LEN: usize> Sealed for Inner256<K, V, PARTIAL_LEN> {}

impl<K, V, const PARTIAL_LEN: usize> Node<PARTIAL_LEN> for Inner256<K, V, PARTIAL_LEN> {
    const TYPE: NodeType = NodeType::Inner256;
    type Key = K;
    type Value = V;
}

impl<K, V, const PARTIAL_LEN: usize> Inner<PARTIAL_LEN> for Inner256<K, V, PARTIAL_LEN> {
    type GrownNode = Self;

    type ShrunkNode = Inner48<K, V, PARTIAL_LEN>;

    fn grow(&self) -> Self::GrownNode {
        todo!()
    }

    fn shrink(&self) -> Self::ShrunkNode {
        todo!()
    }

    fn header(&self) -> &Header<PARTIAL_LEN> {
        todo!()
    }

    fn add(
        &mut self,
        key_partial: u8,
        child_ptr: OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>,
    ) {
        todo!()
    }

    fn del(
        &mut self,
        key_partial: u8,
    ) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>> {
        todo!()
    }

    fn get(&self, key_partial: u8) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>> {
        todo!()
    }

    fn min(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>) {
        todo!()
    }

    fn max(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>) {
        todo!()
    }
}
