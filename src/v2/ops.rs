use std::{marker::PhantomData, ops::ControlFlow};

use crate::v2::{
    key::BytesRepr,
    raw::{Inner, NodePtr},
    search_key::SearchKey,
};

use super::raw::{ConcreteNodePtr, Leaf, OpaqueNodePtr};

pub struct FullPrefixMismatch<K, V, const PARTIAL_LEN: usize> {
    pub mismatch: u8,
    pub prefix_len: usize,
    pub leaf: Option<NodePtr<Leaf<K, V>>>,
}

struct InsertCursor;

enum InsertOp<K, V, const PARTIAL_LEN: usize> {
    Mismatch {
        mismatch: FullPrefixMismatch<K, V, PARTIAL_LEN>,
    },
}

pub struct Ops<K, V, const PARTIAL_LEN: usize>(PhantomData<(K, V)>);

impl<K, V, const PARTIAL_LEN: usize> Ops<K, V, PARTIAL_LEN> {
    pub unsafe fn search_for_insert(
        root: OpaqueNodePtr<K, V, PARTIAL_LEN>,
        search_key: SearchKey<'_>,
    ) -> InsertCursor
    where
        K: BytesRepr,
    {
        #[inline]
        fn visit<T, K, V, const PARTIAL_LEN: usize>(
            current_depth: &mut usize,
            node_ptr: NodePtr<T>,
            search_key: SearchKey<'_>,
        ) -> ControlFlow<
            FullPrefixMismatch<K, V, PARTIAL_LEN>,
            Option<OpaqueNodePtr<K, V, PARTIAL_LEN>>,
        >
        where
            T: Inner<PARTIAL_LEN, Key = K, Value = V>,
            K: BytesRepr,
        {
            let node = unsafe { node_ptr.as_ref() };
            match node.match_full_prefix(search_key, *current_depth) {
                Err(mismatch) => ControlFlow::Break(mismatch),
                Ok(prefix_len) => {
                    *current_depth += prefix_len;
                    ControlFlow::Continue(node.get(search_key[*current_depth]))
                }
            }
        }

        // let mut current_grandparent = None;
        // let mut current_parent = None;
        let mut current_node = root;
        let mut current_depth = 0;

        loop {
            let lookup_result = match current_node.as_concrete() {
                ConcreteNodePtr::Inner4(node_ptr) => {
                    visit(&mut current_depth, node_ptr, search_key)
                }
                ConcreteNodePtr::Inner16(node_ptr) => {
                    visit(&mut current_depth, node_ptr, search_key)
                }
                ConcreteNodePtr::Inner48(node_ptr) => {
                    visit(&mut current_depth, node_ptr, search_key)
                }
                ConcreteNodePtr::Inner256(node_ptr) => {
                    visit(&mut current_depth, node_ptr, search_key)
                }
                ConcreteNodePtr::Leaf(node_ptr) => todo!(),
            };
        }

        todo!()
    }

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
