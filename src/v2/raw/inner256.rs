use crate::v2::Sealed;

use super::{Header, Inner, Inner48, Node, NodeType, OpaqueNodePtr};

#[repr(C)]
pub struct Inner256<K, V, const PARTIAL_LEN: usize> {
    header: Header<PARTIAL_LEN>,
    ptrs: [Option<OpaqueNodePtr<K, V, PARTIAL_LEN>>; 256],
}

impl<K, V, const PARTIAL_LEN: usize> Sealed for Inner256<K, V, PARTIAL_LEN> {}
impl<K, V, const PARTIAL_LEN: usize> From<Header<PARTIAL_LEN>> for Inner256<K, V, PARTIAL_LEN> {
    fn from(header: Header<PARTIAL_LEN>) -> Self {
        Self {
            header,
            ptrs: [None; 256],
        }
    }
}

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
        &self.header
    }

    fn add(
        &mut self,
        key_partial: u8,
        child_ptr: OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>,
    ) {
        if self.ptrs[key_partial as usize].replace(child_ptr).is_none() {
            self.header.children += 1;
        }
    }

    fn del(
        &mut self,
        key_partial: u8,
    ) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>> {
        let deleted = self.ptrs[key_partial as usize].take();
        if deleted.is_some() {
            self.header.children -= 1;
        }
        deleted
    }

    fn get(&self, key_partial: u8) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>> {
        self.ptrs[key_partial as usize]
    }

    fn min(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>) {
        for key in u8::MIN..=u8::MAX {
            if let Some(ptr) = self.ptrs[key as usize] {
                return (key, ptr);
            }
        }
        unreachable!("node is empty")
    }

    fn max(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>) {
        for key in (u8::MIN..=u8::MAX).rev() {
            if let Some(ptr) = self.ptrs[key as usize] {
                return (key, ptr);
            }
        }
        unreachable!("node is empty")
    }
}
