use std::mem::MaybeUninit;

use crate::v2::Sealed;

use super::{Header, Inner, Inner48, Node, NodeType, OpaqueNodePtr};

#[repr(C)]
pub struct InnerSorted<K, V, const PARTIAL_LEN: usize, const NUM_CHILDREN: usize> {
    header: Header<PARTIAL_LEN>,
    keys: [MaybeUninit<u8>; NUM_CHILDREN],
    ptrs: [MaybeUninit<OpaqueNodePtr<K, V, PARTIAL_LEN>>; NUM_CHILDREN],
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
        todo!()
    }

    fn shrink(&self) -> Self::ShrunkNode {
        todo!()
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
    const TYPE: NodeType = NodeType::Inner4;
    type Key = K;
    type Value = V;
}

impl<K, V, const PARTIAL_LEN: usize> Inner<PARTIAL_LEN> for InnerSorted<K, V, PARTIAL_LEN, 16> {
    type GrownNode = Inner48<K, V, PARTIAL_LEN>;
    type ShrunkNode = InnerSorted<K, V, PARTIAL_LEN, 4>;

    fn grow(&self) -> Self::GrownNode {
        todo!()
    }

    fn shrink(&self) -> Self::ShrunkNode {
        todo!()
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

enum Position {
    Exact(usize),
    Shift(usize),
    Last(usize),
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
    fn position(&self, key_partial: u8) -> Position {
        let keys = self.keys();
        if NUM_CHILDREN < 16 {
            match keys.iter().position(|&k| k >= key_partial) {
                None => Position::Last(self.header.children as usize),
                Some(pos) => {
                    if keys[pos] == key_partial {
                        Position::Exact(pos)
                    } else {
                        Position::Shift(pos)
                    }
                }
            }
        } else {
            match keys.binary_search(&key_partial) {
                Ok(pos) => Position::Exact(pos),
                Err(pos) => {
                    if pos < keys.len() {
                        Position::Shift(pos)
                    } else {
                        Position::Last(pos)
                    }
                }
            }
        }
    }

    #[inline]
    fn header(&self) -> &Header<PARTIAL_LEN> {
        &self.header
    }

    #[inline]
    fn add(&mut self, key_partial: u8, child_ptr: OpaqueNodePtr<K, V, PARTIAL_LEN>) {
        let pos = match self.position(key_partial) {
            Position::Exact(pos) => pos,
            Position::Shift(pos) => {
                self.keys[pos..].rotate_right(1);
                self.ptrs[pos..].rotate_right(1);
                pos
            }
            Position::Last(pos) => {
                self.header.children += 1;
                pos
            }
        };
        self.keys[pos].write(key_partial);
        self.ptrs[pos].write(child_ptr);
    }

    #[inline]
    fn del(&mut self, key_partial: u8) -> Option<OpaqueNodePtr<K, V, PARTIAL_LEN>> {
        let Position::Exact(pos) = self.position(key_partial) else {
            return None;
        };
        let child = self.ptrs()[pos];
        self.header.children -= 1;
        self.keys[pos..].rotate_left(1);
        self.ptrs[pos..].rotate_left(1);
        Some(child)
    }

    #[inline]
    fn get(&self, key_partial: u8) -> Option<OpaqueNodePtr<K, V, PARTIAL_LEN>> {
        let Position::Exact(pos) = self.position(key_partial) else {
            return None;
        };
        Some(self.ptrs()[pos])
    }

    #[inline]
    fn min(&self) -> (u8, OpaqueNodePtr<K, V, PARTIAL_LEN>) {
        let keys = self.keys();
        let ptrs = self.ptrs();
        (keys[0], ptrs[0])
    }

    #[inline]
    fn max(&self) -> (u8, OpaqueNodePtr<K, V, PARTIAL_LEN>) {
        let n = self.header.children as usize - 1;
        let keys = self.keys();
        let ptrs = self.ptrs();
        (keys[n], ptrs[n])
    }
}

mod tests {

}
