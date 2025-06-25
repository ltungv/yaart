/// A wrapper around a byte array/vector proving methods for working with [`crate::ART`].
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct SearchKey<K> {
    elems: K,
}

impl<K, T> AsRef<T> for SearchKey<K>
where
    K: AsRef<T>,
    T: ?Sized,
{
    fn as_ref(&self) -> &T {
        self.elems.as_ref()
    }
}

impl<K> IntoIterator for SearchKey<K>
where
    K: IntoIterator,
{
    type Item = K::Item;

    type IntoIter = K::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.elems.into_iter()
    }
}

impl<K> SearchKey<K> {
    /// Returns a new [`SearchKey`] containing some arbitrary elements.
    pub const fn new(elems: K) -> Self {
        Self { elems }
    }

    /// Returns a new [`SearchKey`] refencing the elements of this
    /// [`SearchKey`].
    pub fn into_ref<T>(&self) -> SearchKey<&T>
    where
        K: AsRef<T>,
        T: ?Sized,
    {
        SearchKey {
            elems: self.elems.as_ref(),
        }
    }

    /// Returns whether the [`SearchKey`] is empty.
    pub fn is_empty<T>(&self) -> bool
    where
        K: AsRef<[T]>,
    {
        self.elems.as_ref().is_empty()
    }

    /// Returns the number of elements in the current [`SearchKey`].
    pub fn len<T>(&self) -> usize
    where
        K: AsRef<[T]>,
    {
        self.elems.as_ref().len()
    }

    /// Returns the element at the given position or a default value if the
    /// index is out-of-bounds.
    pub fn get<T>(&self, index: usize) -> T
    where
        K: AsRef<[T]>,
        T: Copy + Default,
    {
        self.elems.as_ref().get(index).copied().unwrap_or_default()
    }

    /// Returns a new [`SearchKey`] containing only the elements starting from
    /// the given index.
    pub fn from<T>(&self, index: usize) -> SearchKey<&[T]>
    where
        K: AsRef<[T]>,
    {
        SearchKey {
            elems: &self.elems.as_ref()[index..],
        }
    }

    /// Returns a number of common elements between the prefix of the two given
    /// search keys.
    pub fn common_prefix_len<Q, T>(&self, other: &SearchKey<Q>, depth: usize) -> usize
    where
        K: AsRef<[T]>,
        Q: AsRef<[T]>,
        T: Eq,
    {
        self.from(depth)
            .into_iter()
            .zip(other.from(depth))
            .take_while(|(x, y)| x == y)
            .count()
    }
}
