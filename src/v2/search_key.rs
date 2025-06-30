use std::ops::Index;

/// A slice of bytes used during tree searches and traversals.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SearchKey<'a> {
    elems: &'a [u8],
}

impl<'a> Index<usize> for SearchKey<'a> {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        self.elems.get(index).unwrap_or(&0)
    }
}

impl AsRef<[u8]> for SearchKey<'_> {
    fn as_ref(&self) -> &[u8] {
        self.elems
    }
}

impl<'a> IntoIterator for SearchKey<'a> {
    type Item = &'a u8;

    type IntoIter = <&'a [u8] as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.elems.into_iter()
    }
}

impl<'a> SearchKey<'a> {
    /// Returns a new [`SearchKey`] over the given slice of bytes.
    pub const fn new(elems: &'a [u8]) -> Self {
        Self { elems }
    }

    /// Returns the length of the slice of bytes.
    pub fn len(self) -> usize {
        self.elems.len()
    }

    /// Returns whether the slice of bytes is empty.
    pub fn is_empty(self) -> bool {
        self.elems.is_empty()
    }

    /// Returns a new search key whose slice starts from the given index.
    pub fn shift(self, index: usize) -> SearchKey<'a> {
        SearchKey {
            elems: &self.elems.as_ref()[index..],
        }
    }

    /// Returns a new search key whose slice starts from the given index and has the given length.
    pub fn range(self, index: usize, len: usize) -> SearchKey<'a> {
        SearchKey {
            elems: &self.elems.as_ref()[index..index + len],
        }
    }

    /// Returns the length of the common prefix between two [`SearchKey`]s.
    pub fn common_prefix_len<'b>(self, other: SearchKey<'b>) -> usize {
        self.into_iter()
            .zip(other)
            .take_while(|(x, y)| x == y)
            .count()
    }
}
