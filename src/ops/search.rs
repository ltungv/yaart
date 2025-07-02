use std::marker::PhantomData;

use crate::{
    raw::{ConcreteNodePtr, Inner, Leaf, NodePtr, OpaqueNodePtr},
    search_key::SearchKey,
    BytesRepr,
};

use super::{PrefixMatch, PrefixMismatch};

enum SearchStrategy {
    Optimistic,
    Pessimistic,
}

impl SearchStrategy {
    pub fn match_prefix<T, const PARTIAL_LEN: usize>(
        &mut self,
        inner: &T,
        key: SearchKey<'_>,
    ) -> Result<PrefixMatch, PrefixMismatch>
    where
        T: Inner<PARTIAL_LEN>,
    {
        let result = match self {
            Self::Optimistic => inner.match_optimistic(key).map(PrefixMatch::Optimistic),
            Self::Pessimistic => inner.match_partial_prefix(key),
        };

        match &result {
            Ok(PrefixMatch::Optimistic(_)) => *self = Self::Optimistic,
            Err(PrefixMismatch { mismatched, .. }) if mismatched.is_none() => {
                *self = Self::Optimistic;
            }
            _ => {}
        }

        result
    }

    pub fn match_leaf<K, V, const PARTIAL_LEN: usize>(
        self,
        leaf: &Leaf<K, V>,
        key: SearchKey<'_>,
        current_depth: usize,
    ) -> bool
    where
        K: BytesRepr,
    {
        match self {
            Self::Pessimistic => {
                let leaf_key = leaf.key.repr();
                let current_depth = current_depth.min(leaf_key.len()).min(key.len());
                leaf_key.shift(current_depth) == key.shift(current_depth)
            }
            Self::Optimistic => leaf.key.repr() == key,
        }
    }
}

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
    pub unsafe fn exact(
        root: OpaqueNodePtr<K, V, PARTIAL_LEN>,
        key: SearchKey<'_>,
    ) -> Option<NodePtr<Leaf<K, V>>>
    where
        K: BytesRepr,
    {
        fn descend<T, K, V, const PARTIAL_LEN: usize>(
            search_strategy: &mut SearchStrategy,
            current_depth: &mut usize,
            node_ptr: NodePtr<T>,
            key: SearchKey<'_>,
        ) -> Option<OpaqueNodePtr<K, V, PARTIAL_LEN>>
        where
            T: Inner<PARTIAL_LEN, Key = K, Value = V>,
            K: BytesRepr,
        {
            let node = unsafe { node_ptr.as_ref() };
            let Ok(matching) = search_strategy.match_prefix(node, key.shift(*current_depth)) else {
                return None;
            };
            *current_depth += match matching {
                PrefixMatch::Pessimistic(n) | PrefixMatch::Optimistic(n) => n,
            };
            let child = node.get(key[*current_depth]);
            if child.is_some() {
                *current_depth += 1;
            }
            child
        }

        let mut search_strategy = SearchStrategy::Pessimistic;
        let mut current_node = root;
        let mut current_depth = 0;

        loop {
            current_node = match current_node.as_concrete() {
                ConcreteNodePtr::Leaf(node_ptr) => {
                    let leaf = unsafe { node_ptr.as_ref() };
                    return search_strategy
                        .match_leaf::<_, _, PARTIAL_LEN>(leaf, key, current_depth)
                        .then_some(node_ptr);
                }
                ConcreteNodePtr::Inner4(node_ptr) => {
                    descend(&mut search_strategy, &mut current_depth, node_ptr, key)
                }
                ConcreteNodePtr::Inner16(node_ptr) => {
                    descend(&mut search_strategy, &mut current_depth, node_ptr, key)
                }
                ConcreteNodePtr::Inner48(node_ptr) => {
                    descend(&mut search_strategy, &mut current_depth, node_ptr, key)
                }
                ConcreteNodePtr::Inner256(node_ptr) => {
                    descend(&mut search_strategy, &mut current_depth, node_ptr, key)
                }
            }?;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        compressed_path::CompressedPath,
        raw::{Header, Inner, Inner256, Inner48, InnerSorted, Leaf, NodePtrGuard},
    };

    use super::Search;

    macro_rules! test_minimum {
        ($name:ident,$T:ty) => {
            #[test]
            fn $name() {
                let mut guard = NodePtrGuard::new();
                let leaf1 = guard.manage(Leaf::new(b"abc1abcde1".to_vec(), 0));
                let leaf2 = guard.manage(Leaf::new(b"abc1abcde2".to_vec(), 0));
                let leaf3 = guard.manage(Leaf::new(b"abc2abcdefg1".to_vec(), 0));
                let leaf4 = guard.manage(Leaf::new(b"abc2abcdefg2".to_vec(), 0));

                let mut inner1 = <$T>::from(Header::<3>::from(CompressedPath::new(b"abc", 5)));
                inner1.add(b'1', leaf1.as_opaque());
                inner1.add(b'2', leaf2.as_opaque());

                let mut inner2 = <$T>::from(Header::<3>::from(CompressedPath::new(b"abc", 7)));
                inner2.add(b'1', leaf3.as_opaque());
                inner2.add(b'2', leaf4.as_opaque());

                let inner1 = guard.manage(inner1);
                let inner2 = guard.manage(inner2);

                let mut root = <$T>::from(Header::<3>::from(CompressedPath::new(b"abc", 3)));
                root.add(b'1', inner1.as_opaque());
                root.add(b'2', inner2.as_opaque());

                let root = guard.manage(root);
                let result = unsafe { Search::minimum(root.as_opaque()) };
                assert_eq!(result, leaf1);
            }
        };
    }

    test_minimum!(inner4_minimum, InnerSorted::<Vec<u8>, usize, 3, 4>);
    test_minimum!(inner16_minimum, InnerSorted::<Vec<u8>, usize, 3, 16>);
    test_minimum!(inner48_minimum, Inner48::<Vec<u8>, usize, 3>);
    test_minimum!(inner256_minimum, Inner256::<Vec<u8>, usize, 3>);
}
