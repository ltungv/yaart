use std::{marker::PhantomData, ops::ControlFlow};

use crate::v2::{
    compressed_path::CompressedPath,
    key::BytesRepr,
    raw::{
        ConcreteInnerNodePtr, ConcreteNodePtr, Header, Inner, InnerSorted, Leaf, NodePtr,
        OpaqueNodePtr,
    },
    search_key::SearchKey,
};

use super::{Branch, FullPrefixMismatch};

pub struct Inserted<'a, K, V, const PARTIAL_LEN: usize> {
    pub leaf: NodePtr<Leaf<K, V>>,
    pub prev: Option<Leaf<K, V>>,
    pub root: OpaqueNodePtr<K, V, PARTIAL_LEN>,
    marker: PhantomData<&'a mut Leaf<K, V>>,
}

#[derive(Debug, PartialEq, Eq)]
enum Strategy<K, V, const PARTIAL_LEN: usize> {
    OverwriteLeafValue {
        leaf: NodePtr<Leaf<K, V>>,
    },
    SplitAtLeaf {
        leaf: NodePtr<Leaf<K, V>>,
        prefix_len: usize,
    },
    AddKeyPartialToInner {
        inner: ConcreteInnerNodePtr<K, V, PARTIAL_LEN>,
    },
    SplitAtInner {
        inner: ConcreteInnerNodePtr<K, V, PARTIAL_LEN>,
        mismatch: FullPrefixMismatch<K, V, PARTIAL_LEN>,
    },
}

#[derive(Debug, PartialEq, Eq)]
pub struct Insert<K, V, const PARTIAL_LEN: usize> {
    depth: usize,
    root: OpaqueNodePtr<K, V, PARTIAL_LEN>,
    grandparent: Option<Branch<K, V, PARTIAL_LEN>>,
    parent: Option<Branch<K, V, PARTIAL_LEN>>,
    strategy: Strategy<K, V, PARTIAL_LEN>,
}

impl<K, V, const PARTIAL_LEN: usize> Insert<K, V, PARTIAL_LEN> {
    #[allow(clippy::too_many_lines)]
    pub unsafe fn apply<'a>(self, key: K, value: V) -> Inserted<'a, K, V, PARTIAL_LEN>
    where
        K: BytesRepr,
    {
        let (new_inner, leaf) = match self.strategy {
            Strategy::OverwriteLeafValue { leaf: leaf_ptr } => {
                let new_leaf = Leaf::new(key, value);
                return Inserted {
                    leaf: leaf_ptr,
                    prev: Some(unsafe { leaf_ptr.as_ptr().replace(new_leaf) }),
                    root: self.root,
                    marker: PhantomData,
                };
            }
            Strategy::SplitAtLeaf {
                leaf: old_leaf,
                prefix_len,
            } => {
                let new_key = key.repr();
                let old_key = {
                    let leaf = unsafe { old_leaf.as_ref() };
                    leaf.key.repr()
                };
                let new_partial_key = new_key[self.depth + prefix_len];
                let old_partial_key = old_key[self.depth + prefix_len];
                let header = Header::from(CompressedPath::new(
                    &new_key.range(self.depth, prefix_len),
                    prefix_len,
                ));
                let new_leaf = NodePtr::alloc(Leaf::new(key, value));
                let mut inner4 = InnerSorted::<K, V, PARTIAL_LEN, 4>::from(header);
                inner4.add(new_partial_key, new_leaf.as_opaque());
                inner4.add(old_partial_key, old_leaf.as_opaque());
                (NodePtr::alloc(inner4).as_opaque(), new_leaf)
            }
            Strategy::AddKeyPartialToInner { inner: inner_ptr } => {
                fn add<T, const PARTIAL_LEN: usize>(
                    inner_ptr: NodePtr<T>,
                    partial_key: u8,
                    leaf_ptr: NodePtr<Leaf<T::Key, T::Value>>,
                ) -> OpaqueNodePtr<T::Key, T::Value, PARTIAL_LEN>
                where
                    T: Inner<PARTIAL_LEN>,
                {
                    let inner = unsafe { inner_ptr.as_mut() };
                    if inner.is_full() {
                        let mut grown_inner = inner.grow();
                        grown_inner.add(partial_key, leaf_ptr.as_opaque());
                        unsafe {
                            NodePtr::dealloc(inner_ptr);
                        };
                        NodePtr::alloc(grown_inner).as_opaque()
                    } else {
                        inner.add(partial_key, leaf_ptr.as_opaque());
                        inner_ptr.as_opaque()
                    }
                }
                let partial_key = key.repr()[self.depth];
                let new_leaf = NodePtr::alloc(Leaf::new(key, value));
                let new_inner = match inner_ptr {
                    ConcreteInnerNodePtr::Inner4(node_ptr) => add(node_ptr, partial_key, new_leaf),
                    ConcreteInnerNodePtr::Inner16(node_ptr) => add(node_ptr, partial_key, new_leaf),
                    ConcreteInnerNodePtr::Inner48(node_ptr) => add(node_ptr, partial_key, new_leaf),
                    ConcreteInnerNodePtr::Inner256(node_ptr) => {
                        add(node_ptr, partial_key, new_leaf)
                    }
                };
                (new_inner, new_leaf)
            }
            Strategy::SplitAtInner {
                inner: inner_ptr,
                mismatch,
            } => {
                let partial_key = key.repr()[self.depth + mismatch.prefix_len];
                let new_leaf = NodePtr::alloc(Leaf::new(key, value));
                let mut inner4 = {
                    let header = unsafe { inner_ptr.header() };
                    InnerSorted::<K, V, PARTIAL_LEN, 4>::from(Header::from(CompressedPath::new(
                        header.path.as_ref(),
                        mismatch.prefix_len,
                    )))
                };

                inner4.add(mismatch.mismatched, inner_ptr.as_opaque());
                inner4.add(partial_key, new_leaf.as_opaque());

                let shrink_len = mismatch.prefix_len + 1;
                {
                    let header = unsafe { inner_ptr.header_mut() };
                    match mismatch.leaf {
                        Some(leaf_ptr) => {
                            let leaf_key = {
                                let leaf = unsafe { leaf_ptr.as_ref() };
                                leaf.key.repr()
                            };
                            header
                                .path
                                .shift_with(shrink_len, leaf_key.shift(self.depth + shrink_len));
                        }
                        None => {
                            header.path.shift(shrink_len);
                        }
                    }
                }
                (NodePtr::alloc(inner4).as_opaque(), new_leaf)
            }
        };
        let root = if let Some(parent_branch) = self.parent {
            match parent_branch.ptr {
                ConcreteInnerNodePtr::Inner4(parent_ptr) => {
                    let parent = unsafe { parent_ptr.as_mut() };
                    parent.add(parent_branch.key, new_inner);
                }
                ConcreteInnerNodePtr::Inner16(parent_ptr) => {
                    let parent = unsafe { parent_ptr.as_mut() };
                    parent.add(parent_branch.key, new_inner);
                }
                ConcreteInnerNodePtr::Inner48(parent_ptr) => {
                    let parent = unsafe { parent_ptr.as_mut() };
                    parent.add(parent_branch.key, new_inner);
                }
                ConcreteInnerNodePtr::Inner256(parent_ptr) => {
                    let parent = unsafe { parent_ptr.as_mut() };
                    parent.add(parent_branch.key, new_inner);
                }
            }
            self.root
        } else {
            new_inner
        };
        Inserted {
            leaf,
            prev: None,
            root,
            marker: PhantomData,
        }
    }

    /// Searches from the root node for a point in the tree where a leaf having the given search
    /// key can be inserted.
    #[allow(clippy::too_many_lines)]
    pub unsafe fn prepare(root: OpaqueNodePtr<K, V, PARTIAL_LEN>, key: SearchKey<'_>) -> Self
    where
        K: BytesRepr,
    {
        /// Traverses along the tree given the current inner node and the search key.
        #[inline]
        fn descend<T, K, V, const PARTIAL_LEN: usize>(
            current_depth: &mut usize,
            node_ptr: NodePtr<T>,
            key: SearchKey<'_>,
        ) -> ControlFlow<
            FullPrefixMismatch<K, V, PARTIAL_LEN>,
            Option<OpaqueNodePtr<K, V, PARTIAL_LEN>>,
        >
        where
            T: Inner<PARTIAL_LEN, Key = K, Value = V>,
            K: BytesRepr,
        {
            let node = unsafe { node_ptr.as_ref() };
            // While inserting, we want to abort immediately when encountering a prefix mismatch.
            // Therefore, we immediately match the search key at the current depth with the full prefix
            // instead of traversing down the tree optimistically.
            match node.match_full_prefix(key, *current_depth) {
                Err(mismatch) => ControlFlow::Break(mismatch),
                Ok(prefix_len) => {
                    *current_depth += prefix_len;
                    ControlFlow::Continue(node.get(key[*current_depth]))
                }
            }
        }

        let mut current_grandparent = None;
        let mut current_parent = None;
        let mut current_node = root;
        let mut current_depth = 0;

        loop {
            let (current_inner, lookup_result) = match current_node.as_concrete() {
                ConcreteNodePtr::Leaf(node_ptr) => {
                    let leaf_key = {
                        let leaf = unsafe { node_ptr.as_ref() };
                        leaf.key.repr()
                    };
                    // Check if the key fully match an existing leaf.
                    let strategy = if leaf_key == key {
                        // If it fully matches, we just need to replace the leaf's value without
                        // changing the tree's structure.
                        Strategy::OverwriteLeafValue { leaf: node_ptr }
                    } else {
                        // There's a mismatch so we create a new inner node having a prefix
                        // covering everything before the mismatch. Then, we create a new leaf and
                        // add it and the existing leaf to the new inner node using their
                        // mismatched values as the partial_key.
                        Strategy::SplitAtLeaf {
                            leaf: node_ptr,
                            prefix_len: leaf_key
                                .shift(current_depth)
                                .common_prefix_len(key.shift(current_depth)),
                        }
                    };
                    break Self {
                        depth: current_depth,
                        root,
                        grandparent: current_grandparent,
                        parent: current_parent,
                        strategy,
                    };
                }
                ConcreteNodePtr::Inner4(node_ptr) => (
                    ConcreteInnerNodePtr::from(node_ptr),
                    descend(&mut current_depth, node_ptr, key),
                ),
                ConcreteNodePtr::Inner16(node_ptr) => (
                    ConcreteInnerNodePtr::from(node_ptr),
                    descend(&mut current_depth, node_ptr, key),
                ),
                ConcreteNodePtr::Inner48(node_ptr) => (
                    ConcreteInnerNodePtr::from(node_ptr),
                    descend(&mut current_depth, node_ptr, key),
                ),
                ConcreteNodePtr::Inner256(node_ptr) => (
                    ConcreteInnerNodePtr::from(node_ptr),
                    descend(&mut current_depth, node_ptr, key),
                ),
            };

            let next_node = match lookup_result {
                ControlFlow::Continue(next_node) => next_node,
                ControlFlow::Break(mismatch) => {
                    // There's a mismatch so we create a new inner node having a prefix covering
                    // everything before the mismatch. Then, we create a new leaf and add it and the
                    // existing inner node to the new inner node using their mismatched values as
                    // the partial_key. The compressed path of the existing inner node will be
                    // adjusted to accomodate all changes.
                    break Self {
                        depth: current_depth,
                        root,
                        grandparent: current_grandparent,
                        parent: current_parent,
                        strategy: Strategy::SplitAtInner {
                            inner: current_inner,
                            mismatch,
                        },
                    };
                }
            };

            let Some(next_node) = next_node else {
                // No mismatching leaf or inner node has been found so far. This means the partial
                // key of the search key at the current depth is unique, so we just need to create a
                // new leaf and add it to the existing inner node.
                break Self {
                    depth: current_depth,
                    root,
                    grandparent: current_grandparent,
                    parent: current_parent,
                    strategy: Strategy::AddKeyPartialToInner {
                        inner: current_inner,
                    },
                };
            };

            // Simply traverses down the tree while tracking the predecessors. The current depth is
            // advanced by one because a single partial key is used to locate the current node
            // within the parent node. Therefore, we can skip it because it's not included in the
            // compressed paths.

            current_grandparent = current_parent;
            current_parent = Some(Branch {
                ptr: current_inner,
                key: key[current_depth],
            });
            current_node = next_node;
            current_depth += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::v2::{
        compressed_path::CompressedPath,
        raw::{Header, Inner, Inner256, Inner48, InnerSorted, Leaf, NodePtrGuard},
        search_key::SearchKey,
    };

    use super::{Branch, FullPrefixMismatch, Insert, Strategy};

    macro_rules! test_prepare {
        ($name:ident,$T:ty) => {
            #[allow(clippy::too_many_lines)]
            #[test]
            fn $name() {
                let mut guard = NodePtrGuard::new();
                let leaf1 = guard.manage(Leaf::new(b"abc1abcde1xyz".to_vec(), 0));
                let leaf2 = guard.manage(Leaf::new(b"abc1abcde2xyz".to_vec(), 0));
                let leaf3 = guard.manage(Leaf::new(b"abc2abcdefg1xyz".to_vec(), 0));
                let leaf4 = guard.manage(Leaf::new(b"abc2abcdefg2xyz".to_vec(), 0));

                let mut inner1 = <$T>::from(Header::<3>::from(CompressedPath::new(b"abc", 5)));
                let mut inner2 = <$T>::from(Header::<3>::from(CompressedPath::new(b"abc", 7)));
                inner1.add(b'1', leaf1.as_opaque());
                inner1.add(b'2', leaf2.as_opaque());
                inner2.add(b'1', leaf3.as_opaque());
                inner2.add(b'2', leaf4.as_opaque());

                let mut root = <$T>::from(Header::<3>::from(CompressedPath::new(b"abc", 3)));
                let inner1 = guard.manage(inner1);
                let inner2 = guard.manage(inner2);
                root.add(b'1', inner1.as_opaque());
                root.add(b'2', inner2.as_opaque());

                let root = guard.manage(root);
                let cases = [
                    (
                        SearchKey::new(b"abc2abcdefg1xyz"),
                        Insert {
                            depth: 12,
                            root: root.as_opaque(),
                            grandparent: Some(Branch {
                                ptr: root.into(),
                                key: b'2',
                            }),
                            parent: Some(Branch {
                                ptr: inner2.into(),
                                key: b'1',
                            }),
                            strategy: Strategy::OverwriteLeafValue { leaf: leaf3 },
                        },
                    ),
                    (
                        SearchKey::new(b"abc1abcde3xyz"),
                        Insert {
                            depth: 9,
                            root: root.as_opaque(),
                            grandparent: None,
                            parent: Some(Branch {
                                ptr: root.into(),
                                key: b'1',
                            }),
                            strategy: Strategy::AddKeyPartialToInner {
                                inner: inner1.into(),
                            },
                        },
                    ),
                    (
                        SearchKey::new(b"abc2abcdefg3xyz"),
                        Insert {
                            depth: 11,
                            root: root.as_opaque(),
                            grandparent: None,
                            parent: Some(Branch {
                                ptr: root.into(),
                                key: b'2',
                            }),
                            strategy: Strategy::AddKeyPartialToInner {
                                inner: inner2.into(),
                            },
                        },
                    ),
                    (
                        SearchKey::new(b"abc3abcdefg"),
                        Insert {
                            depth: 3,
                            root: root.as_opaque(),
                            grandparent: None,
                            parent: None,
                            strategy: Strategy::AddKeyPartialToInner { inner: root.into() },
                        },
                    ),
                    (
                        SearchKey::new(b"abc1abcde1xy"),
                        Insert {
                            depth: 10,
                            root: root.as_opaque(),
                            grandparent: Some(Branch {
                                ptr: root.into(),
                                key: b'1',
                            }),
                            parent: Some(Branch {
                                ptr: inner1.into(),
                                key: b'1',
                            }),
                            strategy: Strategy::SplitAtLeaf {
                                leaf: leaf1,
                                prefix_len: 2,
                            },
                        },
                    ),
                    (
                        SearchKey::new(b"abc1abcxyz"),
                        Insert {
                            depth: 4,
                            root: root.as_opaque(),
                            grandparent: None,
                            parent: Some(Branch {
                                ptr: root.into(),
                                key: b'1',
                            }),
                            strategy: Strategy::SplitAtInner {
                                inner: inner1.into(),
                                mismatch: FullPrefixMismatch {
                                    prefix_len: 3,
                                    mismatched: b'd',
                                    leaf: Some(leaf1),
                                },
                            },
                        },
                    ),
                    (
                        SearchKey::new(b"abc2abcxyz"),
                        Insert {
                            depth: 4,
                            root: root.as_opaque(),
                            grandparent: None,
                            parent: Some(Branch {
                                ptr: root.into(),
                                key: b'2',
                            }),
                            strategy: Strategy::SplitAtInner {
                                inner: inner2.into(),
                                mismatch: FullPrefixMismatch {
                                    prefix_len: 3,
                                    mismatched: b'd',
                                    leaf: Some(leaf3),
                                },
                            },
                        },
                    ),
                ];
                for (key, expected) in cases {
                    let result = unsafe { Insert::prepare(root.as_opaque(), key) };
                    assert_eq!(result, expected);
                }
            }
        };
    }

    test_prepare!(inner4_prepare, InnerSorted::<Vec<u8>, usize, 3, 4>);
    test_prepare!(inner16_prepare, InnerSorted::<Vec<u8>, usize, 3, 16>);
    test_prepare!(inner48_prepare, Inner48::<Vec<u8>, usize, 3>);
    test_prepare!(inner256_prepare, Inner256::<Vec<u8>, usize, 3>);
}
