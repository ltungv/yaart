use std::ops::Index;

use crate::SearchKey;

/// A partial key is used to support path compression. Only a part of the prefix that matches the
/// original key is stored in the inner node.
#[derive(Debug, Clone)]
pub struct CompressedPath<const N: usize> {
    /// The length of the prefix that matches the original key, which can be longer than the length
    /// of the data array.
    prefix_len: usize,
    /// The data array that holds the partial prefix.
    pub partial: [u8; N],
}

impl<const N: usize> Index<usize> for CompressedPath<N> {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        self.partial.get(index).unwrap_or(&0)
    }
}

impl<const N: usize> AsRef<[u8]> for CompressedPath<N> {
    fn as_ref(&self) -> &[u8] {
        &self.partial[..self.partial_len()]
    }
}

impl<const N: usize> CompressedPath<N> {
    /// Creates a new partial key from the given key and prefix length. We only copy at most N
    /// bytes from the key to fill the data array.
    pub fn new(key: &[u8], prefix_len: usize) -> Self {
        let mut path = Self {
            prefix_len,
            partial: [0; N],
        };
        let partial_len = path.partial_len();
        path.partial[..partial_len].copy_from_slice(&key[..partial_len]);
        path
    }

    pub const fn prefix_len(&self) -> usize {
        self.prefix_len
    }

    pub const fn partial_len(&self) -> usize {
        if self.prefix_len() > N {
            N
        } else {
            self.prefix_len
        }
    }

    /// Returns true if the partial key matches the given key. We only check at most N bytes.
    pub fn check(&self, key: SearchKey<&[u8]>, depth: usize) -> bool {
        let partial_len = self.partial_len();
        self.partial[..partial_len]
            .iter()
            .zip(key.from(depth))
            .take_while(|(x, y)| x.eq(y))
            .count()
            .eq(&partial_len)
    }

    /// Returns the position in which this compressed path and the given key differ.
    pub fn mismatch(&self, key: SearchKey<&[u8]>) -> Option<usize> {
        self.partial[..self.partial_len()]
            .iter()
            .zip(key)
            .position(|(x, y)| x != y)
    }

    /// Pushes a single byte into the partial key. If the data array is full, then the byte will
    /// not be written into it. In that case, only the length will be incremented.
    pub const fn push(&mut self, char: u8) {
        if self.prefix_len < N {
            self.partial[self.prefix_len] = char;
        }
        self.prefix_len += 1;
    }

    /// Appends the data from another partial key into this one. We only copy enough bytes to fill
    /// the data array. The length will be incremented by the length of the other partial key.
    pub fn append(&mut self, other: &Self) {
        if self.prefix_len < N {
            let len = other.prefix_len.min(N - self.prefix_len);
            self.partial[self.prefix_len..self.prefix_len + len]
                .copy_from_slice(&other.partial[..len]);
        }
        self.prefix_len += other.prefix_len;
    }

    pub fn shift(&mut self, shift: usize) {
        self.prefix_len -= shift;
        self.partial.copy_within(shift.., 0);
    }

    pub fn shift_with(&mut self, shift: usize, key: SearchKey<&[u8]>) {
        self.prefix_len -= shift;
        let partial_len = self.partial_len();
        self.partial[..partial_len].copy_from_slice(&key.as_ref()[..partial_len]);
    }
}
