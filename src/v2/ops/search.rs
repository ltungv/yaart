use std::marker::PhantomData;

use crate::v2::raw::{ConcreteNodePtr, Inner, Leaf, NodePtr, OpaqueNodePtr};

pub struct Search<K, V, const PARTIAL_LEN: usize>(PhantomData<(K, V)>);

impl<K, V, const PARTIAL_LEN: usize> Search<K, V, PARTIAL_LEN> {
    /// Search for the leaf with the minimum key.
    pub unsafe fn minimum(root: OpaqueNodePtr<K, V, PARTIAL_LEN>) -> NodePtr<Leaf<K, V>> {
        let mut current_node = root;
        loop {
            current_node = match current_node.as_concrete() {
                ConcreteNodePtr::Leaf(node_ptr) => {
                    return node_ptr;
                }
                ConcreteNodePtr::Inner4(node_ptr) => unsafe { node_ptr.as_ref().min().1 },
                ConcreteNodePtr::Inner16(node_ptr) => unsafe { node_ptr.as_ref().min().1 },
                ConcreteNodePtr::Inner48(node_ptr) => unsafe { node_ptr.as_ref().min().1 },
                ConcreteNodePtr::Inner256(node_ptr) => unsafe { node_ptr.as_ref().min().1 },
            }
        }
    }
}
