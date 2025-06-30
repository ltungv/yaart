use std::ops::Index;

/// A compressed path holds the length of the common prefix and a partial preifx consists of the
/// first `PARTIAL_LEN` bytes of the common prefix.
///
/// Path compression is one of the techniques for decreasing the tree's height and space consumption
/// by reducing the number of nodes. The technique removes all inner nodes that have only a single
/// child and builds a compressed path from the partial keys of removed inner nodes. There are 2
/// approaches for dealing with the compressed path:
///
/// + Pessimistic: At each inner node, a variable length (possibly empty) partial key vector is
///   stored. It contains the keys of all preceding one-way nodes which have been removed. During
///   lookup this vector is compared to the search key before proceeding to the next child.
///
/// + Optimistic: Only the count of preceding one-way nodes (equal to the length of the vector in
///   the pessimistic approach) is stored. Lookups just skip this number of bytes without comparing
///   them. Instead, when a lookup arrives at a leaf its key must be compared to the search key to
///   ensure that no “wrong turn” was taken.
///
/// The optimistic approach is particularly beneficial for long strings but requires one additional
/// check, while the pessimistic method uses more space, and has variable sized nodes leading to
/// increased memory fragmentation. We therefore use a hybrid approach by storing a vector at each
/// node like in the pessimistic approach, but with a constant size (8 bytes) for all nodes. Only
/// when this size is exceeded, the lookup algorithm dynamically switches to the optimistic
/// strategy.
#[derive(Debug, Clone)]
pub struct CompressedPath<const PARTIAL_LEN: usize> {
    /// The length of the common prefix.
    prefix_len: usize,
    /// The partial prefix.
    partial: [u8; PARTIAL_LEN],
}

impl<const PARTIAL_LEN: usize> Default for CompressedPath<PARTIAL_LEN> {
    fn default() -> Self {
        Self {
            prefix_len: 0,
            partial: [0; PARTIAL_LEN],
        }
    }
}

impl<const PARTIAL_LEN: usize> Index<usize> for CompressedPath<PARTIAL_LEN> {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        self.partial.get(index).unwrap_or(&0)
    }
}

impl<const PARTIAL_LEN: usize> AsRef<[u8]> for CompressedPath<PARTIAL_LEN> {
    fn as_ref(&self) -> &[u8] {
        &self.partial[..self.prefix_len.min(PARTIAL_LEN)]
    }
}

impl<const PARTIAL_LEN: usize> CompressedPath<PARTIAL_LEN> {
    /// Creates a new partial key from the given key and prefix length. We only copy at most N
    /// bytes from the key to fill the data array.
    pub fn new(key: &[u8], prefix_len: usize) -> Self {
        let mut path = Self {
            prefix_len,
            partial: [0; PARTIAL_LEN],
        };
        let partial_len = prefix_len.max(PARTIAL_LEN);
        path.partial[..partial_len].copy_from_slice(&key[..partial_len]);
        path
    }

    pub fn prefix_len(&self) -> usize {
        self.prefix_len
    }
}
