use std::{cmp, error, fmt, mem::MaybeUninit, usize};

use crate::v2::Sealed;

use super::{Header, Inner, Inner256, InnerSorted, Node, NodeType, OpaqueNodePtr};

#[repr(C)]
pub struct Inner48<K, V, const PARTIAL_LEN: usize> {
    header: Header<PARTIAL_LEN>,
    keys: [RestrictedIndex<48>; 256],
    ptrs: [MaybeUninit<OpaqueNodePtr<K, V, PARTIAL_LEN>>; 48],
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

impl<K, V, const PARTIAL_LEN: usize> Node<PARTIAL_LEN> for Inner48<K, V, PARTIAL_LEN> {
    const TYPE: NodeType = NodeType::Inner48;
    type Key = K;
    type Value = V;
}

impl<K, V, const PARTIAL_LEN: usize> Inner<PARTIAL_LEN> for Inner48<K, V, PARTIAL_LEN> {
    type GrownNode = Inner256<K, V, PARTIAL_LEN>;

    type ShrunkNode = InnerSorted<K, V, PARTIAL_LEN, 16>;

    fn grow(&self) -> Self::GrownNode {
        todo!()
    }

    fn shrink(&self) -> Self::ShrunkNode {
        todo!()
    }

    fn header(&self) -> &Header<PARTIAL_LEN> {
        &self.header
    }

    fn add(
        &mut self,
        key_partial: u8,
        child_ptr: OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>,
    ) {
        let key_partial_index = key_partial as usize;
        let child_index = self.keys[key_partial_index];
        if child_index.is_empty() {
            let child_index = self.header.children as usize;
            self.header.children += 1;
            self.ptrs[child_index].write(child_ptr);
            self.keys[key_partial_index] =
                RestrictedIndex::try_from(child_index).expect("node is not full");
        } else {
            self.ptrs[usize::from(child_index)].write(child_ptr);
        };
    }

    fn del(
        &mut self,
        key_partial: u8,
    ) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>> {
        let key_partial_index = key_partial as usize;
        let child_index = self.keys[key_partial_index];
        if child_index.is_empty() {
            None
        } else {
            self.header.children -= 1;
            self.keys[key_partial_index] = RestrictedIndex::EMPTY;
            Some(unsafe { self.ptrs[usize::from(child_index)].assume_init_read() })
        }
    }

    fn get(&self, key_partial: u8) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>> {
        let key_partial_index = key_partial as usize;
        let child_index = self.keys[key_partial_index];
        if child_index.is_empty() {
            None
        } else {
            Some(unsafe { self.ptrs[usize::from(child_index)].assume_init_read() })
        }
    }

    fn min(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>) {
        for key in u8::MIN..=u8::MAX {
            let child_index = self.keys[key as usize];
            if !child_index.is_empty() {
                let child_ptr = unsafe { self.ptrs[usize::from(child_index)].assume_init_read() };
                return (key, child_ptr);
            }
        }
        unreachable!("node is empty")
    }

    fn max(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>) {
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
enum RestrictedIndexError {
    TryFromByte { limit: u8, value: usize },
}

impl error::Error for RestrictedIndexError {}

impl fmt::Display for RestrictedIndexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RestrictedIndexError::TryFromByte { limit, value } => {
                write!(f, "value is out-of-bound ({value} > {limit})")
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
struct RestrictedIndex<const LIMIT: u8>(u8);

impl<const LIMIT: u8> Default for RestrictedIndex<LIMIT> {
    fn default() -> Self {
        Self::EMPTY
    }
}

impl<const LIMIT: u8> RestrictedIndex<LIMIT> {
    const EMPTY: Self = RestrictedIndex(LIMIT);

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
        usize::from(src.0)
    }
}

impl<const LIMIT: u8> TryFrom<u8> for RestrictedIndex<LIMIT> {
    type Error = RestrictedIndexError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value < LIMIT {
            Ok(RestrictedIndex(value))
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

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        if value < usize::from(LIMIT) {
            Ok(RestrictedIndex(value as u8))
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
