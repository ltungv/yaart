use std::ops::ControlFlow;

use crate::v2::{
    key::BytesRepr,
    raw::{ConcreteInnerNodePtr, ConcreteNodePtr, Inner, Leaf, NodePtr, OpaqueNodePtr},
    search_key::SearchKey,
};

use super::{Branch, FullPrefixMismatch};

enum Op<K, V, const PARTIAL_LEN: usize> {
    OverwriteLeafValue {
        leaf_ptr: NodePtr<Leaf<K, V>>,
    },
    AddKeyPartialToInner {
        inner_ptr: ConcreteInnerNodePtr<K, V, PARTIAL_LEN>,
    },
    SplitAtLeaf {
        leaf_ptr: NodePtr<Leaf<K, V>>,
        prefix_len: usize,
    },
    SplitAtInner {
        inner_ptr: ConcreteInnerNodePtr<K, V, PARTIAL_LEN>,
        mismatch: FullPrefixMismatch<K, V, PARTIAL_LEN>,
    },
}

struct Insert<K, V, const PARTIAL_LEN: usize> {
    depth: usize,
    root: OpaqueNodePtr<K, V, PARTIAL_LEN>,
    grandparent: Option<Branch<K, V, PARTIAL_LEN>>,
    parent: Option<Branch<K, V, PARTIAL_LEN>>,
    op: Op<K, V, PARTIAL_LEN>,
}

impl<K, V, const PARTIAL_LEN: usize> Insert<K, V, PARTIAL_LEN> {
    /// Searches from the root node for a point in the tree where a leaf having the given search
    /// key can be inserted.
    pub unsafe fn prepare(root: OpaqueNodePtr<K, V, PARTIAL_LEN>, search_key: SearchKey<'_>) -> Self
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

        let mut current_grandparent = None;
        let mut current_parent = None;
        let mut current_node = root;
        let mut current_depth = 0;

        loop {
            let (current_inner, lookup_result) = match current_node.as_concrete() {
                ConcreteNodePtr::Inner4(inner_ptr) => (
                    ConcreteInnerNodePtr::from(inner_ptr),
                    visit(&mut current_depth, inner_ptr, search_key),
                ),
                ConcreteNodePtr::Inner16(inner_ptr) => (
                    ConcreteInnerNodePtr::from(inner_ptr),
                    visit(&mut current_depth, inner_ptr, search_key),
                ),
                ConcreteNodePtr::Inner48(inner_ptr) => (
                    ConcreteInnerNodePtr::from(inner_ptr),
                    visit(&mut current_depth, inner_ptr, search_key),
                ),
                ConcreteNodePtr::Inner256(inner_ptr) => (
                    ConcreteInnerNodePtr::from(inner_ptr),
                    visit(&mut current_depth, inner_ptr, search_key),
                ),
                ConcreteNodePtr::Leaf(leaf_ptr) => {
                    let leaf_search_key = {
                        let leaf = unsafe { leaf_ptr.as_ref() };
                        SearchKey::new(leaf.key.repr())
                    };

                    if leaf_search_key == search_key {
                        return Self {
                            depth: current_depth,
                            root,
                            grandparent: current_grandparent,
                            parent: current_parent,
                            op: Op::OverwriteLeafValue { leaf_ptr },
                        };
                    }

                    let prefix_len = leaf_search_key
                        .shift(current_depth)
                        .common_prefix_len(search_key.shift(current_depth));

                    return Self {
                        depth: current_depth,
                        root,
                        grandparent: current_grandparent,
                        parent: current_parent,
                        op: Op::SplitAtLeaf {
                            leaf_ptr,
                            prefix_len,
                        },
                    };
                }
            };
            match lookup_result {
                ControlFlow::Continue(next_node) => match next_node {
                    Some(next_node) => {
                        current_grandparent = current_parent;
                        current_parent = Some(Branch {
                            ptr: current_inner,
                            key: search_key[current_depth],
                        });
                        current_node = next_node;
                        current_depth += 1;
                    }
                    None => {
                        return Self {
                            depth: current_depth,
                            root,
                            grandparent: current_grandparent,
                            parent: current_parent,
                            op: Op::AddKeyPartialToInner {
                                inner_ptr: current_inner,
                            },
                        }
                    }
                },
                ControlFlow::Break(mismatch) => {
                    return Self {
                        depth: current_depth,
                        root,
                        grandparent: current_grandparent,
                        parent: current_parent,
                        op: Op::SplitAtInner {
                            inner_ptr: current_inner,
                            mismatch,
                        },
                    };
                }
            };
        }
    }

    // pub fn apply(self, key: K, value: V)
    // where
    //     K: BytesRepr,
    // {
    //     match self.op {
    //         Op::OverwriteLeafValue { leaf_ptr } => todo!(),
    //         Op::AddKeyPartialToInner { inner_ptr } => todo!(),
    //         Op::SplitAtLeaf {
    //             leaf_ptr,
    //             prefix_len,
    //         } => {
    //             let search_key = SearchKey::new(key.repr());

    //             // SAFETY: We hold a mutable reference, so creating a shared reference is safe
    //             let leaf_search_key = unsafe { SearchKey::new(leaf_ptr.as_ref().key.repr()) };

    //             let mut new_n4 = InnerSorted::<_, _, _, 4>::from(Header::new(
    //                 &key_bytes[key_bytes_used..new_key_bytes_used],
    //                 new_key_bytes_used - key_bytes_used,
    //             ));

    //             let leaf_node_key_byte = leaf_bytes[new_key_bytes_used];
    //             let new_leaf_node_key_byte = key_bytes[new_key_bytes_used];
    //             let new_leaf_node_pointer =
    //                 NodePtr::allocate_node_ptr(LeafNode::with_no_siblings(key, value), alloc);

    //             unsafe {
    //                 // SAFETY: This is a new node 4 so it's empty and we have
    //                 // space for writing new children. We also check the order
    //                 // of the keys before writing
    //                 if leaf_node_key_byte < new_leaf_node_key_byte {
    //                     new_n4.write_child_unchecked(leaf_node_key_byte, leaf_node_ptr.to_opaque());
    //                     new_n4.write_child_unchecked(
    //                         new_leaf_node_key_byte,
    //                         new_leaf_node_pointer.to_opaque(),
    //                     );

    //                     // SAFETY: There is no concurrent modification of the new leaf node, the
    //                     // existing leaf node, or its siblings because of the safety requirements of
    //                     // the `apply` function.
    //                     LeafNode::insert_after(new_leaf_node_pointer, leaf_node_ptr);
    //                 } else {
    //                     new_n4.write_child_unchecked(
    //                         new_leaf_node_key_byte,
    //                         new_leaf_node_pointer.to_opaque(),
    //                     );
    //                     new_n4.write_child_unchecked(leaf_node_key_byte, leaf_node_ptr.to_opaque());

    //                     // SAFETY: There is no concurrent modification of the new leaf node, the
    //                     // existing leaf node, or its siblings because of the safety requirements of
    //                     // the `apply` function.
    //                     LeafNode::insert_before(new_leaf_node_pointer, leaf_node_ptr);
    //                 }
    //             }

    //             (
    //                 NodePtr::allocate_node_ptr(new_n4, alloc).to_opaque(),
    //                 new_leaf_node_pointer,
    //             )
    //         }
    //         Op::SplitAtInner {
    //             inner_ptr,
    //             mismatch,
    //         } => todo!(),
    //     }
    // }
}
