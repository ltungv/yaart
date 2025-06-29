use std::{marker::PhantomData, ops::ControlFlow};

use crate::v2::{
    key::AsSearchKey,
    raw::{Inner, NodePtr},
    search_key::SearchKey,
};

use super::OpaqueNodePtr;

/// Represents a prefix mismatch when looking at the entire prefix, including in
/// cases where it is read from a child leaf node.
pub struct ExplicitMismatch<K, V, const PREFIX_LEN: usize> {
    /// How many bytes were matched
    pub matched_bytes: usize,
    /// Value of the byte that made it not match
    pub prefix_byte: u8,
    /// Pointer to the leaf if the prefix was reconstructed
    pub leaf_ptr: OptionalLeafPtr<K, V, PREFIX_LEN>,
}

struct InsertCursor;

struct Ops<K, V, const PARTIAL_LEN: usize>(PhantomData<(K, V)>);

impl<K, V, const PARTIAL_LEN: usize> Ops<K, V, PARTIAL_LEN> {
    pub unsafe fn search_for_insert(
        root: OpaqueNodePtr<K, V, PARTIAL_LEN>,
        search_key: SearchKey<&[u8]>,
    ) -> InsertCursor {
        #[inline]
        fn test<T, K, V, const PREFIX_LEN: usize>(
            inner_ptr: NodePtr<T>,
            key: &[u8],
            current_depth: &mut usize,
        ) -> ControlFlow<ExplicitMismatch<K, V, PREFIX_LEN>, Option<OpaqueNodePtr<K, V, PREFIX_LEN>>>
        where
            N: Inner<PREFIX_LEN, Key = K, Value = V>,
            K: AsSearchKey,
        {
            let inner_node = unsafe { inner_ptr.as_ref() };
            let match_prefix = inner_node.match_full_prefix(key, *current_depth);
            match match_prefix {
                Err(mismatch) => Ok(ControlFlow::Break(mismatch)),
                Ok(PrefixMatch { matched_bytes }) => {
                    // Since the prefix matched, advance the depth by the size of the prefix
                    *current_depth += matched_bytes;

                    if likely!(*current_depth < key.len()) {
                        let next_key_fragment = key[*current_depth];
                        ControlFlow::Continue(
                            inner_node.lookup_child(next_key_fragment),
                        )
                    } else {
                        // then the key has insufficient bytes to be unique. It must be
                        // a prefix of an existing key
                        Err(InsertPrefixError {
                            byte_repr: key.into(),
                        })
                    }
                }
            }
        }

        todo!()
    }
}
