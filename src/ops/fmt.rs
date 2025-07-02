use std::{fmt, marker::PhantomData};

use crate::{
    raw::{ConcreteNodePtr, Inner, NodePtr, OpaqueNodePtr},
    BytesRepr,
};

pub struct Fmt<K, V, const PARTIAL_LEN: usize>(PhantomData<(K, V)>);

impl<K, V, const PARTIAL_LEN: usize> Fmt<K, V, PARTIAL_LEN> {
    pub unsafe fn debug(
        root: OpaqueNodePtr<K, V, PARTIAL_LEN>,
        f: &mut fmt::Formatter<'_>,
    ) -> fmt::Result
    where
        K: BytesRepr,
        V: fmt::Debug,
    {
        fn visit<T, const PARTIAL_LEN: usize>(
            stack: &mut Vec<(usize, u8, OpaqueNodePtr<T::Key, T::Value, PARTIAL_LEN>)>,
            f: &mut fmt::Formatter<'_>,
            height: usize,
            partial_key: u8,
            node_ptr: NodePtr<T>,
        ) -> fmt::Result
        where
            T: Inner<PARTIAL_LEN>,
            T::Key: BytesRepr,
            T::Value: fmt::Debug,
        {
            let inner = unsafe { node_ptr.as_ref() };
            let indent = "  ".repeat(height);
            for (key, ptr) in inner.iter().rev() {
                stack.push((height + 1, key, ptr));
            }
            writeln!(
                f,
                "{indent} {partial_key:0>3} --> {:?}",
                inner.header().path
            )
        }

        let mut stack = Vec::new();
        stack.push((0, 0, root));
        while let Some((height, partial_key, current_node)) = stack.pop() {
            match current_node.as_concrete() {
                ConcreteNodePtr::Leaf(node_ptr) => {
                    let leaf = unsafe { node_ptr.as_ref() };
                    let indent = "  ".repeat(height);
                    writeln!(f, "{indent} {partial_key:0>3} --> {leaf:?}")?;
                }
                ConcreteNodePtr::Inner4(node_ptr) => {
                    visit(&mut stack, f, height, partial_key, node_ptr)?;
                }
                ConcreteNodePtr::Inner16(node_ptr) => {
                    visit(&mut stack, f, height, partial_key, node_ptr)?;
                }
                ConcreteNodePtr::Inner48(node_ptr) => {
                    visit(&mut stack, f, height, partial_key, node_ptr)?;
                }
                ConcreteNodePtr::Inner256(node_ptr) => {
                    visit(&mut stack, f, height, partial_key, node_ptr)?;
                }
            }
        }
        Ok(())
    }
}
