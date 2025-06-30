use std::{
    hash::Hash,
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

use crate::v2::search_key::SearchKey;

use super::{AsSearchKey, KeyMapping};

#[derive(Debug)]
#[repr(transparent)]
pub struct Mapped<M, T>
where
    M: KeyMapping<T>,
{
    key: M::Key,
    _marker: PhantomData<(M, T)>,
}

impl<M, T> Copy for Mapped<M, T>
where
    M: KeyMapping<T>,
    M::Key: Copy,
{
}

impl<M, T> Clone for Mapped<M, T>
where
    M: KeyMapping<T>,
    M::Key: Clone,
{
    fn clone(&self) -> Self {
        Self::with_key(self.key.clone())
    }
}

impl<M, T> Hash for Mapped<M, T>
where
    M: KeyMapping<T>,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.key.key().as_ref().hash(state);
    }
}

impl<M, T> Eq for Mapped<M, T> where M: KeyMapping<T> {}
impl<M, T> PartialEq for Mapped<M, T>
where
    M: KeyMapping<T>,
{
    fn eq(&self, other: &Self) -> bool {
        self.key.key() == other.key.key()
    }
}

impl<M, T> Deref for Mapped<M, T>
where
    M: KeyMapping<T>,
{
    type Target = M::Key;

    fn deref(&self) -> &Self::Target {
        &self.key
    }
}

impl<M, T> DerefMut for Mapped<M, T>
where
    M: KeyMapping<T>,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.key
    }
}

impl<M, T> AsRef<M::Key> for Mapped<M, T>
where
    M: KeyMapping<T>,
{
    fn as_ref(&self) -> &M::Key {
        self
    }
}

impl<M, T> AsMut<M::Key> for Mapped<M, T>
where
    M: KeyMapping<T>,
{
    fn as_mut(&mut self) -> &mut M::Key {
        self
    }
}

impl<M, T> AsSearchKey for Mapped<M, T>
where
    M: KeyMapping<T>,
{
    fn key(&self) -> SearchKey<'_> {
        self.key.key()
    }
}

impl<M, T> Mapped<M, T>
where
    M: KeyMapping<T>,
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
