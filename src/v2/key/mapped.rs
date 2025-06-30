use std::{
    hash::Hash,
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use super::{BytesMapping, BytesRepr};

#[derive(Debug)]
#[repr(transparent)]
pub struct Mapped<M, T>
where
    M: BytesMapping<T>,
{
    key: M::Key,
    _marker: PhantomData<(M, T)>,
}

impl<M, T> Copy for Mapped<M, T>
where
    M: BytesMapping<T>,
    M::Key: Copy,
{
}

impl<M, T> Clone for Mapped<M, T>
where
    M: BytesMapping<T>,
    M::Key: Clone,
{
    fn clone(&self) -> Self {
        Self::with_key(self.key.clone())
    }
}

impl<M, T> Hash for Mapped<M, T>
where
    M: BytesMapping<T>,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.key.repr().as_ref().hash(state);
    }
}

impl<M, T> Eq for Mapped<M, T> where M: BytesMapping<T> {}
impl<M, T> PartialEq for Mapped<M, T>
where
    M: BytesMapping<T>,
{
    fn eq(&self, other: &Self) -> bool {
        self.key.repr() == other.key.repr()
    }
}

impl<M, T> Deref for Mapped<M, T>
where
    M: BytesMapping<T>,
{
    type Target = M::Key;

    fn deref(&self) -> &Self::Target {
        &self.key
    }
}

impl<M, T> DerefMut for Mapped<M, T>
where
    M: BytesMapping<T>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.key
    }
}

impl<M, T> AsRef<M::Key> for Mapped<M, T>
where
    M: BytesMapping<T>,
{
    fn as_ref(&self) -> &M::Key {
        self
    }
}

impl<M, T> AsMut<M::Key> for Mapped<M, T>
where
    M: BytesMapping<T>,
{
    fn as_mut(&mut self) -> &mut M::Key {
        self
    }
}

impl<M, T> BytesRepr for Mapped<M, T>
where
    M: BytesMapping<T>,
{
    fn repr(&self) -> &[u8] {
        self.key.repr()
    }
}

impl<M, T> Mapped<M, T>
where
    M: BytesMapping<T>,
{
    pub fn new(value: T) -> Self {
        Self::with_key(M::to_bytes(value))
    }

    pub fn with_key(key: M::Key) -> Self {
        Mapped {
            key,
            _marker: PhantomData,
        }
    }

    pub fn get(self) -> T {
        M::from_bytes(self.key)
    }
}
