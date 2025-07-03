use std::ops::{Deref, Index};

/// A slice of bytes used during tree searches and traversals.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SearchKey<'a> {
    elems: &'a [u8],
}

impl<'a> From<&'a [u8]> for SearchKey<'a> {
    fn from(elems: &'a [u8]) -> Self {
        Self::new(elems)
    }
}

impl Deref for SearchKey<'_> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.elems
    }
}

impl Index<usize> for SearchKey<'_> {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        self.elems.get(index).unwrap_or(&0)
    }
}

impl<'a> IntoIterator for SearchKey<'a> {
    type Item = &'a u8;

    type IntoIter = <&'a [u8] as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.elems.iter()
    }
}

impl<'a> SearchKey<'a> {
    /// Returns a new [`SearchKey`] over the given slice of bytes.
    #[must_use]
    pub const fn new(elems: &'a [u8]) -> Self {
        Self { elems }
    }

    /// Returns a new search key whose slice starts from the given index.
    #[must_use]
    pub fn shift(self, index: usize) -> Self {
        SearchKey { elems: &self.elems[index..] }
    }

    /// Returns a new search key whose slice starts from the given index and has the given length.
    #[must_use]
    pub fn range(self, index: usize, len: usize) -> Self {
        SearchKey { elems: &self.elems[index..index + len] }
    }

    /// Returns the length of the common prefix between two [`SearchKey`]s.
    #[must_use]
    pub fn common_prefix_len(self, other: SearchKey<'_>) -> usize {
        self.into_iter().zip(other).take_while(|(x, y)| x == y).count()
    }
}

#[cfg(test)]
mod tests {
    use super::SearchKey;

    #[test]
    fn basic_properties() {
        let k = SearchKey::new(b"");
        assert!(k.is_empty());
        assert_eq!(k.len(), 0);
        assert_eq!(&*k, b"".as_slice());

        let k = SearchKey::new(b"abc");
        assert!(!k.is_empty());
        assert_eq!(k.len(), 3);
        assert_eq!(&*k, b"abc".as_slice());
    }

    #[test]
    fn shift() {
        let k1 = SearchKey::new(b"abcdef");
        let k2 = k1.shift(3);
        assert!(!k2.is_empty());
        assert_eq!(k2.len(), 3);
        assert_eq!(&*k2, b"def".as_slice());
    }

    #[test]
    fn range() {
        let k1 = SearchKey::new(b"abcdef");
        let k2 = k1.range(1, 4);
        assert!(!k2.is_empty());
        assert_eq!(k2.len(), 4);
        assert_eq!(&*k2, b"bcde".as_slice());
    }

    #[test]
    fn common_prefix_len() {
        let k1 = SearchKey::new(b"abcdef");
        let k2 = SearchKey::new(b"abcabc");
        assert_eq!(k1.common_prefix_len(k2), 3);
    }
}
