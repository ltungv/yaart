use crate::{raw::RestrictedIndex, Sealed};

use super::{Header, Inner, Inner48, Node, NodeType, OpaqueNodePtr};

#[derive(Debug)]
#[repr(C)]
pub struct Inner256<K, V, const PARTIAL_LEN: usize> {
    pub(crate) header: Header<PARTIAL_LEN>,
    pub(crate) ptrs: [Option<OpaqueNodePtr<K, V, PARTIAL_LEN>>; 256],
}

impl<K, V, const PARTIAL_LEN: usize> Sealed for Inner256<K, V, PARTIAL_LEN> {}
impl<K, V, const PARTIAL_LEN: usize> From<Header<PARTIAL_LEN>> for Inner256<K, V, PARTIAL_LEN> {
    fn from(header: Header<PARTIAL_LEN>) -> Self {
        Self {
            header,
            ptrs: [None; 256],
        }
    }
}

impl<'a, K, V, const PARTIAL_LEN: usize> IntoIterator for &'a Inner256<K, V, PARTIAL_LEN> {
    type Item = (u8, OpaqueNodePtr<K, V, PARTIAL_LEN>);

    type IntoIter = Inner256Iter<'a, K, V, PARTIAL_LEN>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            offset: 0,
            length: self.header.children as usize,
            inner: self,
        }
    }
}

impl<K, V, const PARTIAL_LEN: usize> Node<PARTIAL_LEN> for Inner256<K, V, PARTIAL_LEN> {
    const TYPE: NodeType = NodeType::Inner256;
    type Key = K;
    type Value = V;
}

impl<K, V, const PARTIAL_LEN: usize> Inner<PARTIAL_LEN> for Inner256<K, V, PARTIAL_LEN> {
    type GrownNode = Self;

    type ShrunkNode = Inner48<K, V, PARTIAL_LEN>;

    type Iter<'a>
        = Inner256Iter<'a, K, V, PARTIAL_LEN>
    where
        Self: 'a;

    fn grow(&self) -> Self::GrownNode {
        unreachable!("grow is impossible")
    }

    fn shrink(&self) -> Self::ShrunkNode {
        let mut shrunk = Self::ShrunkNode::from(self.header.clone());
        let mut index = 0;
        for key in u8::MIN..=u8::MAX {
            if let Some(child) = self.ptrs[key as usize] {
                let child_index = RestrictedIndex::try_from(index).expect("index is within bounds");
                shrunk.keys[key as usize] = child_index;
                shrunk.ptrs[index].write(child);
                index += 1;
            }
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
        if self.ptrs[partial_key as usize].replace(child_ptr).is_none() {
            self.header.children += 1;
        }
    }

    fn del(&mut self, partial_key: u8) -> Option<OpaqueNodePtr<K, V, PARTIAL_LEN>> {
        let deleted = self.ptrs[partial_key as usize].take();
        if deleted.is_some() {
            self.header.children -= 1;
        }
        deleted
    }

    fn get(&self, partial_key: u8) -> Option<OpaqueNodePtr<K, V, PARTIAL_LEN>> {
        self.ptrs[partial_key as usize]
    }

    fn min(&self) -> (u8, OpaqueNodePtr<K, V, PARTIAL_LEN>) {
        for key in u8::MIN..=u8::MAX {
            if let Some(ptr) = self.ptrs[key as usize] {
                return (key, ptr);
            }
        }
        unreachable!("node is empty")
    }

    fn max(&self) -> (u8, OpaqueNodePtr<K, V, PARTIAL_LEN>) {
        for key in (u8::MIN..=u8::MAX).rev() {
            if let Some(ptr) = self.ptrs[key as usize] {
                return (key, ptr);
            }
        }
        unreachable!("node is empty")
    }
}

#[derive(Debug)]
pub struct Inner256Iter<'a, K, V, const PARTIAL_LEN: usize> {
    offset: usize,
    length: usize,
    inner: &'a Inner256<K, V, PARTIAL_LEN>,
}

impl<K, V, const PARTIAL_LEN: usize> ExactSizeIterator for Inner256Iter<'_, K, V, PARTIAL_LEN> {
    fn len(&self) -> usize {
        self.length
    }
}

impl<K, V, const PARTIAL_LEN: usize> DoubleEndedIterator for Inner256Iter<'_, K, V, PARTIAL_LEN> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.length == 0 {
            return None;
        }
        while self.length > 0 {
            let key = self.offset + self.length - 1;
            let ptr = self.inner.ptrs[key];
            self.length -= 1;
            if let Some(ptr) = ptr {
                let key = u8::try_from(key).expect("partial key must be an u8");
                return Some((key, ptr));
            }
        }
        None
    }
}

impl<K, V, const PARTIAL_LEN: usize> Iterator for Inner256Iter<'_, K, V, PARTIAL_LEN> {
    type Item = (u8, OpaqueNodePtr<K, V, PARTIAL_LEN>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.length == 0 {
            return None;
        }
        while self.length > 0 {
            let key = self.offset;
            let ptr = self.inner.ptrs[key];
            self.offset += 1;
            self.length -= 1;
            if let Some(ptr) = ptr {
                let key = u8::try_from(key).expect("partial key must be an u8");
                return Some((key, ptr));
            }
        }
        None
    }
}
