use std::{cmp, error, fmt, mem::MaybeUninit};

use crate::v2::Sealed;

use super::{Header, Inner, Inner256, InnerSorted, Node, NodeType, OpaqueNodePtr};

#[derive(Debug)]
#[repr(C)]
pub struct Inner48<K, V, const PARTIAL_LEN: usize> {
    pub(crate) header: Header<PARTIAL_LEN>,
    pub(crate) keys: [RestrictedIndex<48>; 256],
    pub(crate) ptrs: [MaybeUninit<OpaqueNodePtr<K, V, PARTIAL_LEN>>; 48],
}

impl<K, V, const PARTIAL_LEN: usize> Sealed for Inner48<K, V, PARTIAL_LEN> {}

impl<K, V, const PARTIAL_LEN: usize> From<Header<PARTIAL_LEN>> for Inner48<K, V, PARTIAL_LEN> {
    fn from(header: Header<PARTIAL_LEN>) -> Self {
        Self {
            header,
            keys: [RestrictedIndex::EMPTY; 256],
            ptrs: unsafe { MaybeUninit::uninit().assume_init() },
        }
    }
}

impl<'a, K, V, const PARTIAL_LEN: usize> IntoIterator for &'a Inner48<K, V, PARTIAL_LEN> {
    type Item = (u8, OpaqueNodePtr<K, V, PARTIAL_LEN>);

    type IntoIter = Inner48Iter<'a, K, V, PARTIAL_LEN>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            offset: 0,
            length: self.header.children as usize,
            inner: self,
        }
    }
}

impl<K, V, const PARTIAL_LEN: usize> Node<PARTIAL_LEN> for Inner48<K, V, PARTIAL_LEN> {
    const TYPE: NodeType = NodeType::Inner48;
    type Key = K;
    type Value = V;
}

impl<K, V, const PARTIAL_LEN: usize> Inner<PARTIAL_LEN> for Inner48<K, V, PARTIAL_LEN> {
    type GrownNode = Inner256<K, V, PARTIAL_LEN>;

    type ShrunkNode = InnerSorted<K, V, PARTIAL_LEN, 16>;

    type Iter<'a>
        = Inner48Iter<'a, K, V, PARTIAL_LEN>
    where
        Self: 'a;

    fn grow(&self) -> Self::GrownNode {
        let mut grown = Self::GrownNode::from(self.header.clone());
        for key in 0..256 {
            let child_index = self.keys[key];
            if child_index.is_empty() {
                continue;
            }
            let child = unsafe { self.ptrs[usize::from(child_index)].assume_init_read() };
            grown.ptrs[key] = Some(child);
        }
        grown
    }

    fn shrink(&self) -> Self::ShrunkNode {
        let mut shrunk = Self::ShrunkNode::from(self.header.clone());
        let mut index = 0;
        for key in u8::MIN..=u8::MAX {
            let child_index = self.keys[key as usize];
            if child_index.is_empty() {
                continue;
            }
            let child = unsafe { self.ptrs[usize::from(child_index)].assume_init_read() };
            shrunk.keys[index].write(key);
            shrunk.ptrs[index].write(child);
            index += 1;
        }
        shrunk
    }

    fn iter(&self) -> Self::Iter<'_> {
        self.into_iter()
    }

    fn header(&self) -> &Header<PARTIAL_LEN> {
        &self.header
    }

    fn add(&mut self, partial_key: u8, child_ptr: OpaqueNodePtr<K, V, PARTIAL_LEN>) {
        let partial_key_index = partial_key as usize;
        let child_index = self.keys[partial_key_index];
        if child_index.is_empty() {
            let child_index = self.header.children as usize;
            self.header.children += 1;
            self.ptrs[child_index].write(child_ptr);
            self.keys[partial_key_index] =
                RestrictedIndex::try_from(child_index).expect("index is within bounds");
        } else {
            self.ptrs[usize::from(child_index)].write(child_ptr);
        }
    }

    fn del(&mut self, partial_key: u8) -> Option<OpaqueNodePtr<K, V, PARTIAL_LEN>> {
        let partial_key_index = partial_key as usize;
        let child_index = self.keys[partial_key_index];
        if child_index.is_empty() {
            None
        } else {
            self.header.children -= 1;
            self.keys[partial_key_index] = RestrictedIndex::EMPTY;
            Some(unsafe { self.ptrs[usize::from(child_index)].assume_init_read() })
        }
    }

    fn get(&self, partial_key: u8) -> Option<OpaqueNodePtr<K, V, PARTIAL_LEN>> {
        let partial_key_index = partial_key as usize;
        let child_index = self.keys[partial_key_index];
        if child_index.is_empty() {
            None
        } else {
            Some(unsafe { self.ptrs[usize::from(child_index)].assume_init_read() })
        }
    }

    fn min(&self) -> (u8, OpaqueNodePtr<K, V, PARTIAL_LEN>) {
        for key in u8::MIN..=u8::MAX {
            let child_index = self.keys[key as usize];
            if !child_index.is_empty() {
                let child_ptr = unsafe { self.ptrs[usize::from(child_index)].assume_init_read() };
                return (key, child_ptr);
            }
        }
        unreachable!("node is empty")
    }

    fn max(&self) -> (u8, OpaqueNodePtr<K, V, PARTIAL_LEN>) {
        for key in (u8::MIN..=u8::MAX).rev() {
            let child_index = self.keys[key as usize];
            if !child_index.is_empty() {
                let child_ptr = unsafe { self.ptrs[usize::from(child_index)].assume_init_read() };
                return (key, child_ptr);
            }
        }
        unreachable!("node is empty")
    }
}

#[derive(Debug)]
pub struct Inner48Iter<'a, K, V, const PARTIAL_LEN: usize> {
    offset: usize,
    length: usize,
    inner: &'a Inner48<K, V, PARTIAL_LEN>,
}

impl<K, V, const PARTIAL_LEN: usize> ExactSizeIterator for Inner48Iter<'_, K, V, PARTIAL_LEN> {
    fn len(&self) -> usize {
        self.length
    }
}

impl<K, V, const PARTIAL_LEN: usize> DoubleEndedIterator for Inner48Iter<'_, K, V, PARTIAL_LEN> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.length == 0 {
            return None;
        }
        while self.length > 0 {
            let key = self.offset + self.length - 1;
            let ptr_index = self.inner.keys[key];
            self.length -= 1;
            if !ptr_index.is_empty() {
                let key = u8::try_from(key).expect("partial key must be an u8");
                let ptr = unsafe { self.inner.ptrs[usize::from(ptr_index)].assume_init_read() };
                return Some((key, ptr));
            }
        }
        None
    }
}

impl<K, V, const PARTIAL_LEN: usize> Iterator for Inner48Iter<'_, K, V, PARTIAL_LEN> {
    type Item = (u8, OpaqueNodePtr<K, V, PARTIAL_LEN>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.length == 0 {
            return None;
        }
        while self.length > 0 {
            let key = self.offset;
            let ptr_index = self.inner.keys[key];
            self.offset += 1;
            self.length -= 1;
            if !ptr_index.is_empty() {
                let key = u8::try_from(key).expect("partial key must be an u8");
                let ptr = unsafe { self.inner.ptrs[usize::from(ptr_index)].assume_init_read() };
                return Some((key, ptr));
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.length, Some(self.length))
    }
}

#[derive(Debug)]
pub enum RestrictedIndexError {
    TryFromByte { limit: u8, value: usize },
}

impl error::Error for RestrictedIndexError {}

impl fmt::Display for RestrictedIndexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TryFromByte { limit, value } => {
                write!(f, "value is out-of-bound ({value} > {limit})")
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct RestrictedIndex<const LIMIT: u8>(u8);

impl<const LIMIT: u8> Default for RestrictedIndex<LIMIT> {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl<const LIMIT: u8> RestrictedIndex<LIMIT> {
    const EMPTY: Self = Self(LIMIT);

    fn is_empty(self) -> bool {
        self == Self::EMPTY
    }
}

impl<const LIMIT: u8> From<RestrictedIndex<LIMIT>> for u8 {
    fn from(src: RestrictedIndex<LIMIT>) -> Self {
        src.0
    }
}

impl<const LIMIT: u8> From<RestrictedIndex<LIMIT>> for usize {
    fn from(src: RestrictedIndex<LIMIT>) -> Self {
        Self::from(src.0)
    }
}

impl<const LIMIT: u8> TryFrom<u8> for RestrictedIndex<LIMIT> {
    type Error = RestrictedIndexError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value < LIMIT {
            Ok(Self(value))
        } else {
            Err(RestrictedIndexError::TryFromByte {
                limit: LIMIT,
                value: value as usize,
            })
        }
    }
}

impl<const LIMIT: u8> TryFrom<usize> for RestrictedIndex<LIMIT> {
    type Error = RestrictedIndexError;

    #[allow(clippy::cast_possible_truncation)]
    fn try_from(value: usize) -> Result<Self, Self::Error> {
        if value < usize::from(LIMIT) {
            Ok(Self(value as u8))
        } else {
            Err(RestrictedIndexError::TryFromByte {
                limit: LIMIT,
                value,
            })
        }
    }
}

impl<const LIMIT: u8> PartialOrd for RestrictedIndex<LIMIT> {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        if self.0 == LIMIT || other.0 == LIMIT {
            None
        } else {
            Some(self.0.cmp(&other.0))
        }
    }
}
