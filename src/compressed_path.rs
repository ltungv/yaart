use std::ops::Index;

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
        &self.partial[..self.prefix_len.min(N)]
    }
}

impl<const N: usize> CompressedPath<N> {
    /// Creates a new partial key from the given key and prefix length. We only copy at most N
    /// bytes from the key to fill the data array.
    pub fn new(key: &[u8], len: usize) -> Self {
        let partial_len = len.min(N);
        let mut data = [0; N];
        data[..partial_len].copy_from_slice(&key[..partial_len]);
        Self {
            prefix_len: len,
            partial: data,
        }
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

    /// Returns true if the partial key matches the given key. We only check at most N bytes.
    pub fn match_key(&self, key: &[u8], depth: usize) -> bool {
        let partial_len = self.prefix_len.min(N);
        self.partial[..partial_len]
            .iter()
            .zip(key[depth..].iter())
            .take_while(|(x, y)| x.eq(y))
            .count()
            .eq(&partial_len)
    }

    pub const fn prefix_len(&self) -> usize {
        self.prefix_len
    }

    pub fn shift(&mut self, shift: usize) {
        self.prefix_len -= shift;
        self.partial.copy_within(shift.., 0);
    }

    pub fn shift_with(&mut self, shift: usize, key: &[u8]) {
        self.prefix_len -= shift;
        self.partial[..self.prefix_len.min(N)].copy_from_slice(&key[..self.prefix_len.min(N)]);
    }

    pub fn mismatch(&self, key: &[u8]) -> Option<usize> {
        self.partial[..self.prefix_len.min(N)]
            .iter()
            .zip(key.iter())
            .position(|(x, y)| x != y)
    }
}
