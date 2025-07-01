use std::mem::MaybeUninit;

use crate::v2::{raw::RestrictedIndex, Sealed};

use super::{Header, Inner, Inner48, Node, NodeType, OpaqueNodePtr};

#[repr(C)]
pub struct InnerSorted<K, V, const PARTIAL_LEN: usize, const NUM_CHILDREN: usize> {
    pub(crate) header: Header<PARTIAL_LEN>,
    pub(crate) keys: [MaybeUninit<u8>; NUM_CHILDREN],
    pub(crate) ptrs: [MaybeUninit<OpaqueNodePtr<K, V, PARTIAL_LEN>>; NUM_CHILDREN],
}

impl<K, V, const PARTIAL_LEN: usize, const NUM_CHILDREN: usize> Sealed
    for InnerSorted<K, V, PARTIAL_LEN, NUM_CHILDREN>
{
}

impl<K, V, const PARTIAL_LEN: usize, const NUM_CHILDREN: usize> From<Header<PARTIAL_LEN>>
    for InnerSorted<K, V, PARTIAL_LEN, NUM_CHILDREN>
{
    fn from(header: Header<PARTIAL_LEN>) -> Self {
        Self {
            header,
            keys: unsafe { MaybeUninit::uninit().assume_init() },
            ptrs: unsafe { MaybeUninit::uninit().assume_init() },
        }
    }
}

impl<K, V, const PARTIAL_LEN: usize> Node<PARTIAL_LEN> for InnerSorted<K, V, PARTIAL_LEN, 4> {
    const TYPE: NodeType = NodeType::Inner4;
    type Key = K;
    type Value = V;
}

impl<K, V, const PARTIAL_LEN: usize> Inner<PARTIAL_LEN> for InnerSorted<K, V, PARTIAL_LEN, 4> {
    type GrownNode = InnerSorted<K, V, PARTIAL_LEN, 16>;
    type ShrunkNode = Self;

    fn grow(&self) -> Self::GrownNode {
        let children = self.header.children as usize;
        let mut grown = Self::GrownNode::from(self.header.clone());
        grown.keys[..children].copy_from_slice(&self.keys[..children]);
        grown.ptrs[..children].copy_from_slice(&self.ptrs[..children]);
        grown
    }

    fn shrink(&self) -> Self::ShrunkNode {
        unreachable!("shrink is impossible")
    }

    fn header(&self) -> &Header<PARTIAL_LEN> {
        self.header()
    }

    fn add(
        &mut self,
        key_partial: u8,
        child_ptr: OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>,
    ) {
        self.add(key_partial, child_ptr);
    }

    fn del(
        &mut self,
        key_partial: u8,
    ) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>> {
        self.del(key_partial)
    }

    fn get(&self, key_partial: u8) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>> {
        self.get(key_partial)
    }

    fn min(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>) {
        self.min()
    }

    fn max(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>) {
        self.max()
    }
}

impl<K, V, const PARTIAL_LEN: usize> Node<PARTIAL_LEN> for InnerSorted<K, V, PARTIAL_LEN, 16> {
    const TYPE: NodeType = NodeType::Inner16;
    type Key = K;
    type Value = V;
}

impl<K, V, const PARTIAL_LEN: usize> Inner<PARTIAL_LEN> for InnerSorted<K, V, PARTIAL_LEN, 16> {
    type GrownNode = Inner48<K, V, PARTIAL_LEN>;
    type ShrunkNode = InnerSorted<K, V, PARTIAL_LEN, 4>;

    fn grow(&self) -> Self::GrownNode {
        let mut grown = Self::GrownNode::from(self.header.clone());
        for (index, key) in self.keys().iter().copied().enumerate() {
            let child_index = RestrictedIndex::try_from(index).expect("index is within bounds");
            grown.keys[usize::from(key)] = child_index;
        }
        let children = self.header.children as usize;
        grown.ptrs[..children].copy_from_slice(&self.ptrs[..children]);
        grown
    }

    fn shrink(&self) -> Self::ShrunkNode {
        let children = self.header.children as usize;
        let mut shrunk = Self::ShrunkNode::from(self.header.clone());
        shrunk.keys[..children].copy_from_slice(&self.keys[..children]);
        shrunk.ptrs[..children].copy_from_slice(&self.ptrs[..children]);
        shrunk
    }

    fn header(&self) -> &Header<PARTIAL_LEN> {
        self.header()
    }

    fn add(
        &mut self,
        key_partial: u8,
        child_ptr: OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>,
    ) {
        self.add(key_partial, child_ptr);
    }

    fn del(
        &mut self,
        key_partial: u8,
    ) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>> {
        self.del(key_partial)
    }

    fn get(&self, key_partial: u8) -> Option<OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>> {
        self.get(key_partial)
    }

    fn min(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>) {
        self.min()
    }

    fn max(&self) -> (u8, OpaqueNodePtr<Self::Key, Self::Value, PARTIAL_LEN>) {
        self.max()
    }
}

enum SearchResult {
    Found(usize),
    Insert(usize),
    NotFound(usize),
}

impl<K, V, const PARTIAL_LEN: usize, const NUM_CHILDREN: usize>
    InnerSorted<K, V, PARTIAL_LEN, NUM_CHILDREN>
{
    #[inline]
    fn keys(&self) -> &[u8] {
        let keys = &self.keys[..self.header.children as usize];
        let base_ptr = keys.as_ptr().cast::<u8>();
        unsafe { std::slice::from_raw_parts(base_ptr, keys.len()) }
    }

    #[inline]
    fn ptrs(&self) -> &[OpaqueNodePtr<K, V, PARTIAL_LEN>] {
        let ptrs = &self.ptrs[..self.header.children as usize];
        let base_ptr = ptrs.as_ptr().cast::<OpaqueNodePtr<K, V, PARTIAL_LEN>>();
        unsafe { std::slice::from_raw_parts(base_ptr, ptrs.len()) }
    }

    #[inline]
    fn search(&self, key_partial: u8) -> SearchResult {
        let keys = self.keys();
        if NUM_CHILDREN < 16 {
            keys.iter().position(|&k| k >= key_partial).map_or_else(
                || SearchResult::NotFound(self.header.children as usize),
                |pos| {
                    if keys[pos] == key_partial {
                        SearchResult::Found(pos)
                    } else {
                        SearchResult::Insert(pos)
                    }
                },
            )
        } else {
            keys.binary_search(&key_partial).map_or_else(
                |pos| {
                    if pos < keys.len() {
                        SearchResult::Insert(pos)
                    } else {
                        SearchResult::NotFound(pos)
                    }
                },
                SearchResult::Found,
            )
        }
    }

    #[inline]
    const fn header(&self) -> &Header<PARTIAL_LEN> {
        &self.header
    }

    #[inline]
    fn add(&mut self, key_partial: u8, child_ptr: OpaqueNodePtr<K, V, PARTIAL_LEN>) {
        let pos = match self.search(key_partial) {
            SearchResult::Found(pos) => pos,
            SearchResult::Insert(pos) => {
                println!("{pos}");
                let len = self.header.children as usize;
                self.header.children += 1;
                self.keys.copy_within(pos..len, pos + 1);
                self.ptrs.copy_within(pos..len, pos + 1);
                pos
            }
            SearchResult::NotFound(pos) => {
                self.header.children += 1;
                pos
            }
        };
        self.keys[pos].write(key_partial);
        self.ptrs[pos].write(child_ptr);
    }

    #[inline]
    fn del(&mut self, key_partial: u8) -> Option<OpaqueNodePtr<K, V, PARTIAL_LEN>> {
        let SearchResult::Found(pos) = self.search(key_partial) else {
            return None;
        };
        let child = self.ptrs()[pos];
        let len = self.header.children as usize;
        self.header.children -= 1;
        self.keys.copy_within(pos + 1..len, pos);
        self.ptrs.copy_within(pos + 1..len, pos);
        Some(child)
    }

    #[inline]
    fn get(&self, key_partial: u8) -> Option<OpaqueNodePtr<K, V, PARTIAL_LEN>> {
        let SearchResult::Found(pos) = self.search(key_partial) else {
            return None;
        };
        Some(self.ptrs()[pos])
    }

    #[inline]
    fn min(&self) -> (u8, OpaqueNodePtr<K, V, PARTIAL_LEN>) {
        assert_ne!(self.header.children, 0, "node is empty");
        let keys = self.keys();
        let ptrs = self.ptrs();
        (keys[0], ptrs[0])
    }

    #[inline]
    fn max(&self) -> (u8, OpaqueNodePtr<K, V, PARTIAL_LEN>) {
        assert_ne!(self.header.children, 0, "node is empty");
        let n = self.header.children as usize - 1;
        let keys = self.keys();
        let ptrs = self.ptrs();
        (keys[n], ptrs[n])
    }
}
