use std::marker::PhantomData;

use crate::raw::{ConcreteNodePtr, Inner, NodePtr, OpaqueNodePtr};

pub struct Ptr<K, V, const PARTIAL_LEN: usize>(PhantomData<(K, V)>);

impl<K, V, const PARTIAL_LEN: usize> Ptr<K, V, PARTIAL_LEN> {
    pub unsafe fn dealloc(root: OpaqueNodePtr<K, V, PARTIAL_LEN>) {
        fn visit<T, const PARTIAL_LEN: usize>(
            stack: &mut Vec<OpaqueNodePtr<T::Key, T::Value, PARTIAL_LEN>>,
            node_ptr: NodePtr<T>,
        ) where
            T: Inner<PARTIAL_LEN>,
        {
            let inner = unsafe { node_ptr.as_ref() };
            for (_, ptr) in inner.iter() {
                stack.push(ptr);
            }
            unsafe {
                NodePtr::dealloc(node_ptr);
            }
        }

        let mut stack = Vec::new();
        stack.push(root);
        while let Some(current_node) = stack.pop() {
            match current_node.as_concrete() {
                ConcreteNodePtr::Leaf(node_ptr) => unsafe {
                    NodePtr::dealloc(node_ptr);
                },
                ConcreteNodePtr::Inner4(node_ptr) => {
                    visit(&mut stack, node_ptr);
                }
                ConcreteNodePtr::Inner16(node_ptr) => {
                    visit(&mut stack, node_ptr);
                }
                ConcreteNodePtr::Inner48(node_ptr) => {
                    visit(&mut stack, node_ptr);
                }
                ConcreteNodePtr::Inner256(node_ptr) => {
                    visit(&mut stack, node_ptr);
                }
            }
        }
    }
}
