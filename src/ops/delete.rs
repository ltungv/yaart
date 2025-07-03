use crate::{
    compressed_path::CompressedPath,
    ops::SearchStrategy,
    raw::{ConcreteInnerNodePtr, ConcreteNodePtr, Inner, Leaf, NodePtr, OpaqueNodePtr},
    BytesRepr, SearchKey,
};

use super::{Branch, Stateless};

pub struct Deleted<K, V, const PARTIAL_LEN: usize> {
    pub root: Option<OpaqueNodePtr<K, V, PARTIAL_LEN>>,
    pub leaf: Leaf<K, V>,
}

pub struct Delete<K, V, const PARTIAL_LEN: usize> {
    grandparent: Option<Branch<K, V, PARTIAL_LEN>>,
    parent: Option<Branch<K, V, PARTIAL_LEN>>,
    leaf: NodePtr<Leaf<K, V>>,
}

impl<K, V, const PARTIAL_LEN: usize> Delete<K, V, PARTIAL_LEN> {
    pub unsafe fn apply(self, root: OpaqueNodePtr<K, V, PARTIAL_LEN>) -> Deleted<K, V, PARTIAL_LEN> {
        fn remove_and_compress<T, const PARTIAL_LEN: usize>(
            node_ptr: NodePtr<T>,
            partial_key: u8,
        ) -> Option<OpaqueNodePtr<T::Key, T::Value, PARTIAL_LEN>>
        where
            T: Inner<PARTIAL_LEN>,
        {
            let inner = unsafe { node_ptr.as_mut() };
            inner.del(partial_key).expect("child must exist");
            if inner.is_singleton() {
                let (child_partial_key, child_node_ptr) = {
                    let mut children = inner.iter();
                    let child = children.next().expect("a single child");
                    assert!(children.next().is_none(), "expected only a single child, not more");
                    child
                };
                if let Some(child_header) = unsafe { child_node_ptr.header_mut() } {
                    let header = inner.header();
                    let mut path = CompressedPath::default();
                    path.append(header.path.as_partial_prefix(), header.path.prefix_len());
                    path.append(&[child_partial_key], 1);
                    path.append(child_header.path.as_partial_prefix(), child_header.path.prefix_len());
                    child_header.path = path;
                }
                unsafe {
                    drop(NodePtr::dealloc(node_ptr));
                }
                Some(child_node_ptr)
            } else if inner.is_shrinkable() {
                let new_node_ptr = NodePtr::alloc(inner.shrink());
                unsafe {
                    drop(NodePtr::dealloc(node_ptr));
                }
                Some(new_node_ptr.as_opaque())
            } else {
                None
            }
        }

        let root = match (self.parent, self.grandparent) {
            (None, Some(_)) => {
                unreachable!("can not have a grandparent without a parent");
            }
            (None, None) => None,
            (Some(parent), grandparent) => {
                let new_parent_ptr = match parent.ptr {
                    ConcreteInnerNodePtr::Inner4(node_ptr) => remove_and_compress(node_ptr, parent.key),
                    ConcreteInnerNodePtr::Inner16(node_ptr) => remove_and_compress(node_ptr, parent.key),
                    ConcreteInnerNodePtr::Inner48(node_ptr) => remove_and_compress(node_ptr, parent.key),
                    ConcreteInnerNodePtr::Inner256(node_ptr) => remove_and_compress(node_ptr, parent.key),
                };
                let new_root = match (new_parent_ptr, grandparent) {
                    (None, _) => root,
                    (Some(new_parent_ptr), None) => new_parent_ptr,
                    (Some(new_parent_ptr), Some(grandparent)) => {
                        match grandparent.ptr {
                            ConcreteInnerNodePtr::Inner4(node_ptr) => {
                                let inner = unsafe { node_ptr.as_mut() };
                                inner.add(grandparent.key, new_parent_ptr);
                            }
                            ConcreteInnerNodePtr::Inner16(node_ptr) => {
                                let inner = unsafe { node_ptr.as_mut() };
                                inner.add(grandparent.key, new_parent_ptr);
                            }
                            ConcreteInnerNodePtr::Inner48(node_ptr) => {
                                let inner = unsafe { node_ptr.as_mut() };
                                inner.add(grandparent.key, new_parent_ptr);
                            }
                            ConcreteInnerNodePtr::Inner256(node_ptr) => {
                                let inner = unsafe { node_ptr.as_mut() };
                                inner.add(grandparent.key, new_parent_ptr);
                            }
                        }
                        root
                    }
                };
                Some(new_root)
            }
        };
        Deleted { root, leaf: unsafe { NodePtr::dealloc(self.leaf) } }
    }

    pub unsafe fn prepare(root: OpaqueNodePtr<K, V, PARTIAL_LEN>, key: SearchKey<'_>) -> Option<Self>
    where
        K: BytesRepr,
    {
        let mut search_strategy = SearchStrategy::Pessimistic;
        let mut current_grandparent = None;
        let mut current_parent = None;
        let mut current_node = root;
        let mut current_depth = 0;
        loop {
            let (current_inner, next_node) = match current_node.as_concrete() {
                ConcreteNodePtr::Leaf(node_ptr) => {
                    let leaf = unsafe { node_ptr.as_ref() };
                    break search_strategy.match_leaf::<_, _, PARTIAL_LEN>(leaf, key, current_depth).then_some(Self {
                        grandparent: current_grandparent,
                        parent: current_parent,
                        leaf: node_ptr,
                    });
                }
                ConcreteNodePtr::Inner4(node_ptr) => (ConcreteInnerNodePtr::from(node_ptr), unsafe {
                    Stateless::descend(&mut search_strategy, &mut current_depth, node_ptr, key)?
                }),
                ConcreteNodePtr::Inner16(node_ptr) => (ConcreteInnerNodePtr::from(node_ptr), unsafe {
                    Stateless::descend(&mut search_strategy, &mut current_depth, node_ptr, key)?
                }),
                ConcreteNodePtr::Inner48(node_ptr) => (ConcreteInnerNodePtr::from(node_ptr), unsafe {
                    Stateless::descend(&mut search_strategy, &mut current_depth, node_ptr, key)?
                }),
                ConcreteNodePtr::Inner256(node_ptr) => (ConcreteInnerNodePtr::from(node_ptr), unsafe {
                    Stateless::descend(&mut search_strategy, &mut current_depth, node_ptr, key)?
                }),
            };
            current_grandparent = current_parent;
            current_parent = Some(Branch { ptr: current_inner, key: key[current_depth - 1] });
            current_node = next_node;
        }
    }
}
