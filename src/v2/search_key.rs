#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SearchKey<'a> {
    elems: &'a [u8],
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
    /// Returns a new [`SearchKey`] containing some arbitrary elements.
    pub const fn new(elems: &'a [u8]) -> Self {
        Self { elems }
    }

    pub fn len(self) -> usize {
        self.elems.len()
    }

    pub fn is_empty(self) -> bool {
        self.elems.is_empty()
    }

    pub fn get(self, index: usize) -> u8 {
        self.elems.get(index).copied().unwrap_or_default()
    }

    pub fn shift(self, index: usize) -> SearchKey<'a> {
        SearchKey {
            elems: &self.elems.as_ref()[index..],
        }
    }

    pub fn range(self, index: usize, len: usize) -> SearchKey<'a> {
        SearchKey {
            elems: &self.elems.as_ref()[index..index + len],
        }
    }

    pub fn common_prefix_len<'b>(self, other: SearchKey<'b>, depth: usize) -> usize {
        self.shift(depth)
            .into_iter()
            .zip(other.shift(depth))
            .take_while(|(x, y)| x == y)
            .count()
    }
}
