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


impl<'a> Deref for SearchKey<'_> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.elems
    }
}

impl<'a> Index<usize> for SearchKey<'a> {
    type Output = u8;

    fn index(&self, index: usize) -> &Self::Output {
        self.elems.get(index).unwrap_or(&0)
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
