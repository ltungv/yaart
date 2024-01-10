use std::mem::MaybeUninit;

pub trait Indices<T> {
    fn len(&self) -> usize;

    fn is_full(&self) -> bool;

    fn del_child(&mut self, key: u8) -> Option<T>;

    fn add_child(&mut self, key: u8, child: T);

    fn child_ref(&self, key: u8) -> Option<&T>;

    fn child_mut(&mut self, key: u8) -> Option<&mut T>;

    fn min(&self) -> Option<&T>;

    fn max(&self) -> Option<&T>;
}

#[derive(Debug)]
pub struct Sorted<T, const N: usize> {
    len: u8,
    keys: [u8; N],
    children: [MaybeUninit<T>; N],
}

impl<T, const N: usize> Default for Sorted<T, N> {
    fn default() -> Self {
        Self {
            len: 0,
            keys: [0; N],
            children: make_uninitialized_array(),
        }
    }
}

impl<T, const N: usize> Indices<T> for Sorted<T, N> {
    fn len(&self) -> usize {
        self.len as usize
    }

    fn is_full(&self) -> bool {
        self.len() >= N
    }

    fn del_child(&mut self, key: u8) -> Option<T> {
        if N > 4 {
            self.search_binary(key)
        } else {
            self.search_linear(key)
        }
        .map(|idx| {
            let mut child = MaybeUninit::uninit();
            std::mem::swap(&mut child, &mut self.children[idx]);
            self.len -= 1;
            self.keys[idx..].rotate_left(1);
            self.children[idx..].rotate_left(1);
            // SAFETY: Children at index less than `len` must have been initialized.
            unsafe { child.assume_init() }
        })
    }

    fn add_child(&mut self, key: u8, child: T) {
        let idx = if N > 4 {
            let mut l = 0;
            let mut r = self.len as usize;
            while l < r {
                let m = l + (r - l) / 2;
                if self.keys[m] == key {
                    break;
                }
                if self.keys[m] < key {
                    l = m + 1;
                } else {
                    r = m;
                }
            }
            l
        } else {
            self.keys[..self.len as usize]
                .iter()
                .take_while(|&&k| k < key)
                .count()
        };
        self.len += 1;
        self.keys[idx..].rotate_right(1);
        self.keys[idx] = key;
        self.children[idx..].rotate_right(1);
        self.children[idx].write(child);
    }

    fn child_ref(&self, key: u8) -> Option<&T> {
        if N > 4 {
            self.search_binary(key)
        } else {
            self.search_linear(key)
        }
        .map(|idx| unsafe {
            // SAFETY: Children at index less than `len` must have been initialized.
            self.children[idx].assume_init_ref()
        })
    }

    fn child_mut(&mut self, key: u8) -> Option<&mut T> {
        if N > 4 {
            self.search_binary(key)
        } else {
            self.search_linear(key)
        }
        .map(|idx| unsafe {
            // SAFETY: Children at index less than `len` must have been initialized.
            self.children[idx].assume_init_mut()
        })
    }

    fn min(&self) -> Option<&T> {
        self.children[..self.len as usize].first().map(|x| unsafe {
            // SAFETY: Children at index less than `len` must have been initialized.
            x.assume_init_ref()
        })
    }

    fn max(&self) -> Option<&T> {
        self.children[..self.len as usize].last().map(|x| unsafe {
            // SAFETY: Children at index less than `len` must have been initialized.
            x.assume_init_ref()
        })
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a Sorted<T, N> {
    type Item = (u8, &'a T);

    type IntoIter = SortedIter<'a, T, N>;

    fn into_iter(self) -> Self::IntoIter {
        SortedIter {
            indices: self,
            idx: 0,
        }
    }
}

impl<T, const N: usize> Sorted<T, N> {
    pub const fn byte_at(&self, idx: usize) -> u8 {
        self.keys[idx]
    }

    pub fn consume_sorted<const M: usize>(&mut self, other: &mut Sorted<T, M>) {
        for i in 0..other.len as usize {
            self.keys[i] = other.keys[i];
            std::mem::swap(&mut self.children[i], &mut other.children[i]);
        }
        self.len = other.len;
        other.len = 0;
    }

    pub fn consume_indirect<const M: usize>(&mut self, other: &mut Indirect<T, M>) {
        self.len = 0;
        for key in 0..=255 {
            if let Some(idx) = other.indices[key as usize] {
                let pos = self.len as usize;
                self.len += 1;
                self.keys[pos] = key;
                std::mem::swap(&mut self.children[pos], &mut other.children[idx as usize]);
            }
        }
        other.len = 0;
    }

    fn search_linear(&self, key: u8) -> Option<usize> {
        self.keys[..self.len as usize]
            .iter()
            .position(|&k| k == key)
    }

    const fn search_binary(&self, key: u8) -> Option<usize> {
        let mut l = 0;
        let mut r = self.len as usize;
        while l < r {
            let m = l + (r - l) / 2;
            if self.keys[m] == key {
                return Some(m);
            }
            if self.keys[m] < key {
                l = m + 1;
            } else {
                r = m;
            }
        }
        None
    }
}

#[derive(Debug)]
pub struct SortedIter<'a, T, const N: usize> {
    indices: &'a Sorted<T, N>,
    idx: usize,
}

impl<'a, T, const N: usize> Iterator for SortedIter<'a, T, N> {
    type Item = (u8, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.indices.len as usize {
            return None;
        }
        let key = self.indices.keys[self.idx];
        // SAFETY: Children at index less than `len` must have been initialized.
        let child = unsafe { self.indices.children[self.idx].assume_init_ref() };
        self.idx += 1;
        Some((key, child))
    }
}

#[derive(Debug)]
pub struct Indirect<T, const N: usize> {
    len: u8,
    indices: [Option<u8>; 256],
    children: [MaybeUninit<T>; N],
}

impl<T, const N: usize> Default for Indirect<T, N> {
    fn default() -> Self {
        Self {
            len: 0,
            indices: [None; 256],
            children: make_uninitialized_array(),
        }
    }
}

impl<T, const N: usize> Indices<T> for Indirect<T, N> {
    fn len(&self) -> usize {
        self.len as usize
    }

    fn is_full(&self) -> bool {
        self.len as usize >= N
    }

    fn del_child(&mut self, key: u8) -> Option<T> {
        self.indices[key as usize].take().map(|idx| {
            self.len -= 1;
            let mut tmp = MaybeUninit::uninit();
            std::mem::swap(&mut tmp, &mut self.children[idx as usize]);
            // SAFETY: If we found Some(index), the corresponding child must have been initialized.
            unsafe { tmp.assume_init() }
        })
    }

    fn add_child(&mut self, key: u8, child: T) {
        self.children[self.len as usize].write(child);
        if self.indices[key as usize].replace(self.len).is_none() {
            self.len += 1;
        }
    }

    fn child_ref(&self, key: u8) -> Option<&T> {
        self.indices[key as usize].map(|idx| {
            // SAFETY: If we found Some(index), the corresponding child must have been initialized.
            unsafe { self.children[idx as usize].assume_init_ref() }
        })
    }

    fn child_mut(&mut self, key: u8) -> Option<&mut T> {
        self.indices[key as usize].map(|idx| {
            // SAFETY: If we found Some(index), the corresponding child must have been initialized.
            unsafe { self.children[idx as usize].assume_init_mut() }
        })
    }

    fn min(&self) -> Option<&T> {
        self.indices.iter().flatten().next().map(|&idx| {
            // SAFETY: If we found Some(index), the corresponding child must have been initialized.
            unsafe { self.children[idx as usize].assume_init_ref() }
        })
    }

    fn max(&self) -> Option<&T> {
        self.indices.iter().rev().flatten().next().map(|&idx| {
            // SAFETY: If we found Some(index), the corresponding child must have been initialized.
            unsafe { self.children[idx as usize].assume_init_ref() }
        })
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a Indirect<T, N> {
    type Item = (u8, &'a T);

    type IntoIter = IndirectIter<'a, T, N>;

    fn into_iter(self) -> Self::IntoIter {
        IndirectIter {
            indices: self,
            idx: 0,
        }
    }
}

impl<T, const N: usize> Indirect<T, N> {
    pub fn consume_sorted<const M: usize>(&mut self, other: &mut Sorted<T, M>) {
        for idx in 0..other.len {
            let pos = idx as usize;
            self.indices[other.keys[pos] as usize] = Some(idx);
            std::mem::swap(&mut self.children[pos], &mut other.children[pos]);
        }
        self.len = other.len;
        other.len = 0;
    }

    pub fn consume_direct(&mut self, other: &mut Direct<T>) {
        self.len = 0;
        for (key, child) in other.children.iter_mut().enumerate() {
            if let Some(child) = child.take() {
                self.indices[key] = Some(self.len);
                self.children[self.len as usize].write(child);
                self.len += 1;
            }
        }
    }
}

#[derive(Debug)]
pub struct IndirectIter<'a, T, const N: usize> {
    indices: &'a Indirect<T, N>,
    idx: usize,
}

impl<'a, T, const N: usize> Iterator for IndirectIter<'a, T, N> {
    type Item = (u8, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let key = u8::try_from(self.idx).ok()?;
            self.idx += 1;
            if let Some(child) = &self.indices.child_ref(key) {
                return Some((key, child));
            }
        }
    }
}

#[derive(Debug)]
pub struct Direct<T> {
    len: u16,
    children: [Option<T>; 256],
}

impl<T> Default for Direct<T> {
    fn default() -> Self {
        Self {
            len: 0,
            children: [Self::DEFAULT_CHILD; 256],
        }
    }
}

impl<T> Indices<T> for Direct<T> {
    fn len(&self) -> usize {
        self.len as usize
    }

    fn is_full(&self) -> bool {
        self.len as usize >= 256
    }

    fn del_child(&mut self, key: u8) -> Option<T> {
        self.children[key as usize].take().map(|child| {
            self.len -= 1;
            child
        })
    }

    fn add_child(&mut self, key: u8, child: T) {
        if self.children[key as usize].replace(child).is_none() {
            self.len += 1;
        }
    }

    fn child_ref(&self, key: u8) -> Option<&T> {
        self.children[key as usize].as_ref()
    }

    fn child_mut(&mut self, key: u8) -> Option<&mut T> {
        self.children[key as usize].as_mut()
    }

    fn min(&self) -> Option<&T> {
        self.children.iter().flatten().next()
    }

    fn max(&self) -> Option<&T> {
        self.children.iter().rev().flatten().next()
    }
}

impl<'a, T> IntoIterator for &'a Direct<T> {
    type Item = (u8, &'a T);

    type IntoIter = DirectIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        DirectIter {
            indices: self,
            idx: 0,
        }
    }
}

impl<T> Direct<T> {
    pub fn consume_indirect<const N: usize>(&mut self, other: &mut Indirect<T, N>) {
        self.len = 0;
        for key in 0..256 {
            self.children[key] = other.indices[key].map(|idx| {
                self.len += 1;
                let mut tmp = MaybeUninit::uninit();
                std::mem::swap(&mut tmp, &mut other.children[idx as usize]);
                // SAFETY: If we found Some(index), the corresponding child must have been initialized.
                unsafe { tmp.assume_init() }
            });
        }
        other.len = 0;
    }
}

#[derive(Debug)]
pub struct DirectIter<'a, T> {
    indices: &'a Direct<T>,
    idx: usize,
}

impl<'a, T> Iterator for DirectIter<'a, T> {
    type Item = (u8, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < 256 {
            let key = u8::try_from(self.idx).ok()?;
            self.idx += 1;
            if let Some(child) = &self.indices.child_ref(key) {
                return Some((key, child));
            }
        }
        None
    }
}

impl<T> Direct<T> {
    const DEFAULT_CHILD: Option<T> = None;
}

fn make_uninitialized_array<T, const N: usize>() -> [MaybeUninit<T>; N] {
    // SAFETY: calling `assume_init` to convert an uninitialized array
    // into an array of uninitialized items is safe.
    unsafe { MaybeUninit::uninit().assume_init() }
}

#[cfg(test)]
mod tests {
    use crate::indices::{Direct, Indices, Indirect, Sorted};

    #[test]
    fn test_sorted_indices_set_child() {
        let mut indices = Sorted::<usize, 16>::default();
        for i in 0..16 {
            indices.add_child(i, i as usize);
            assert_eq!(indices.len(), i as usize + 1);
        }
        assert!(indices.is_full());
    }

    #[test]
    fn test_sorted4_indices_get_child() {
        let mut indices = Sorted::<usize, 4>::default();
        for i in 0..4 {
            indices.add_child(i, i as usize);
        }
        for i in 0..4 {
            let child = indices.child_ref(i).unwrap();
            assert_eq!(*child, i as usize);
        }
        assert!(indices.child_ref(4).is_none());
    }

    #[test]
    fn test_sorted16_indices_get_child() {
        let mut indices = Sorted::<usize, 16>::default();
        for i in 0..16 {
            indices.add_child(i, i as usize);
        }
        for i in 0..16 {
            let child = indices.child_ref(i).unwrap();
            assert_eq!(*child, i as usize);
        }
        assert!(indices.child_ref(16).is_none());
    }

    #[test]
    fn test_sorted_indices_min_max_child() {
        let mut indices = Sorted::<usize, 16>::default();
        for i in 0..16 {
            indices.add_child(i, i as usize);
            let min_child = indices.min().unwrap();
            let max_child = indices.max().unwrap();
            assert_eq!(*min_child, 0);
            assert_eq!(*max_child, i as usize);
        }

        let mut indices = Sorted::<usize, 16>::default();
        for i in (0..16).rev() {
            indices.add_child(i, i as usize);
            let min_child = indices.min().unwrap();
            let max_child = indices.max().unwrap();
            assert_eq!(*min_child, i as usize);
            assert_eq!(*max_child, 15);
        }
    }

    #[test]
    fn test_sorted4_indices_del_child() {
        let mut indices = Sorted::<usize, 4>::default();
        for i in 0..4 {
            indices.add_child(i, i as usize);
        }
        for i in (0..2).rev() {
            assert_eq!(indices.del_child(i), Some(i as usize));
        }
        for i in (0..2).rev() {
            assert_eq!(indices.del_child(i), None);
        }
        for (i, (k, x)) in (2..4).zip(&indices) {
            assert_eq!(i, k);
            assert_eq!(i as usize, *x);
        }
        assert!(!indices.is_full());
        assert_eq!(indices.len(), 2);
        assert_eq!(indices.into_iter().count(), 2);
    }

    #[test]
    fn test_sorted16_indices_del_child() {
        let mut indices = Sorted::<usize, 16>::default();
        for i in 0..16 {
            indices.add_child(i, i as usize);
        }
        for i in (0..8).rev() {
            assert_eq!(indices.del_child(i), Some(i as usize));
        }
        for i in (0..8).rev() {
            assert_eq!(indices.del_child(i), None);
        }
        for (i, (k, x)) in (8..16).zip(&indices) {
            assert_eq!(i, k);
            assert_eq!(i as usize, *x);
        }
        assert!(!indices.is_full());
        assert_eq!(indices.len(), 8);
        assert_eq!(indices.into_iter().count(), 8);
    }

    #[test]
    fn test_sorted_indices_iter() {
        let mut indices = Sorted::<usize, 16>::default();
        for i in 0..8 {
            indices.add_child(i, i as usize);
        }
        for (i, (key, child)) in indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_indirect_indices_set_child() {
        let mut indices = Indirect::<usize, 48>::default();
        for i in 0..48 {
            indices.add_child(i, i as usize);
            assert_eq!(indices.len(), i as usize + 1);
        }
        assert!(indices.is_full());
    }

    #[test]
    fn test_indirect_indices_get_child() {
        let mut indices = Indirect::<usize, 48>::default();
        for i in 0..48 {
            indices.add_child(i, i as usize);
        }
        for i in 0..48 {
            let child = indices.child_ref(i).unwrap();
            assert_eq!(*child, i as usize);
        }
        assert!(indices.child_ref(48).is_none());
    }

    #[test]
    fn test_indirect_indices_min_max_child() {
        let mut indices = Indirect::<usize, 48>::default();
        for i in 0..48 {
            indices.add_child(i, i as usize);
            let min_child = indices.min().unwrap();
            let max_child = indices.max().unwrap();
            assert_eq!(*min_child, 0);
            assert_eq!(*max_child, i as usize);
        }

        let mut indices = Indirect::<usize, 48>::default();
        for i in (0..48).rev() {
            indices.add_child(i, i as usize);
            let min_child = indices.min().unwrap();
            let max_child = indices.max().unwrap();
            assert_eq!(*min_child, i as usize);
            assert_eq!(*max_child, 47);
        }
    }

    #[test]
    fn test_indirect_indices_del_child() {
        let mut indices = Indirect::<usize, 48>::default();
        for i in 0..48 {
            indices.add_child(i, i as usize);
        }
        for i in (0..24).rev() {
            assert_eq!(indices.del_child(i), Some(i as usize));
        }
        for i in (0..24).rev() {
            assert_eq!(indices.del_child(i), None);
        }
        for (i, (k, x)) in (24..48).zip(&indices) {
            assert_eq!(i, k);
            assert_eq!(i as usize, *x);
        }
        assert!(!indices.is_full());
        assert_eq!(indices.len(), 24);
        assert_eq!(indices.into_iter().count(), 24);
    }

    #[test]
    fn test_indirect_indices_iter() {
        let mut indices = Indirect::<usize, 48>::default();
        for i in 0..24 {
            indices.add_child(i, i as usize);
        }
        for (i, (key, child)) in indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_direct_indices_set_child() {
        let mut indices = Direct::<usize>::default();
        for i in 0..=255 {
            indices.add_child(i, i as usize);
            assert_eq!(indices.len(), i as usize + 1);
        }
        assert!(indices.is_full());
    }

    #[test]
    fn test_direct_indices_get_child() {
        let mut indices = Direct::<usize>::default();
        for i in 0..=255 {
            indices.add_child(i, i as usize);
        }
        for i in 0..=255 {
            let child = indices.child_ref(i).unwrap();
            assert_eq!(*child, i as usize);
        }
    }

    #[test]
    fn test_direct_indices_min_max_child() {
        let mut indices = Direct::<usize>::default();
        for i in 0..=255 {
            indices.add_child(i, i as usize);
            let min_child = indices.min().unwrap();
            let max_child = indices.max().unwrap();
            assert_eq!(*min_child, 0);
            assert_eq!(*max_child, i as usize);
        }

        let mut indices = Direct::<usize>::default();
        for i in (0..=255).rev() {
            indices.add_child(i, i as usize);
            let min_child = indices.min().unwrap();
            let max_child = indices.max().unwrap();
            assert_eq!(*min_child, i as usize);
            assert_eq!(*max_child, 255);
        }
    }

    #[test]
    fn test_direct_indices_del_child() {
        let mut indices = Direct::<usize>::default();
        for i in 0..=255 {
            indices.add_child(i, i as usize);
        }
        for i in (0..128).rev() {
            assert_eq!(indices.del_child(i), Some(i as usize));
        }
        for i in (0..128).rev() {
            assert_eq!(indices.del_child(i), None);
        }
        for (i, (k, x)) in (128..=255).zip(&indices) {
            assert_eq!(i, k);
            assert_eq!(i as usize, *x);
        }
        assert!(!indices.is_full());
        assert_eq!(indices.len(), 128);
        assert_eq!(indices.into_iter().count(), 128);
    }

    #[test]
    fn test_direct_indices_iter() {
        let mut indices = Direct::<usize>::default();
        for i in 0..128 {
            indices.add_child(i, i as usize);
        }
        for (i, (key, child)) in indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_sorted_from_sorted() {
        let mut indices = Sorted::<usize, 4>::default();
        for i in 0..4 {
            indices.add_child(i, i as usize);
        }
        let mut new_indices = Sorted::<usize, 16>::default();
        new_indices.consume_sorted(&mut indices);
        for (i, (key, child)) in new_indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_sorted_from_indirect() {
        let mut indices = Indirect::<usize, 48>::default();
        for i in 0..16 {
            indices.add_child(i, i as usize);
        }
        let mut new_indices = Sorted::<usize, 16>::default();
        new_indices.consume_indirect(&mut indices);
        for (i, (key, child)) in new_indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_indirect_from_sorted() {
        let mut indices = Sorted::<usize, 16>::default();
        for i in 0..16 {
            indices.add_child(i, i as usize);
        }
        let mut new_indices = Indirect::<usize, 48>::default();
        new_indices.consume_sorted(&mut indices);
        for (i, (key, child)) in new_indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_indirect_from_direct() {
        let mut indices = Direct::<usize>::default();
        for i in 0..48 {
            indices.add_child(i, i as usize);
        }
        let mut new_indices = Indirect::<usize, 48>::default();
        new_indices.consume_direct(&mut indices);
        for (i, (key, child)) in new_indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_direct_from_indirect() {
        let mut indices = Indirect::<usize, 48>::default();
        for i in 0..48 {
            indices.add_child(i, i as usize);
        }
        let mut new_indices = Direct::<usize>::default();
        new_indices.consume_indirect(&mut indices);
        for (i, (key, child)) in new_indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }
}
