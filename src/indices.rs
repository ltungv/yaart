use std::mem::MaybeUninit;

pub trait Indices<T> {
    fn is_full(&self) -> bool;

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
    fn is_full(&self) -> bool {
        self.len as usize >= N
    }

    fn add_child(&mut self, key: u8, child: T) {
        debug_assert!((self.len as usize) < N);
        let idx = self.keys[..self.len as usize]
            .iter()
            .take_while(|&&k| k < key)
            .count();

        self.keys[idx..].rotate_right(1);
        self.children[idx..].rotate_right(1);
        self.keys[idx] = key;
        self.children[idx].write(child);
        self.len += 1;
    }

    fn child_ref(&self, key: u8) -> Option<&T> {
        self.keys[..self.len as usize]
            .iter()
            .position(|&k| k == key)
            .map(|idx| {
                // SAFETY: Children at index less than `len` must have been initialized.
                unsafe { self.children[idx].assume_init_ref() }
            })
    }

    fn child_mut(&mut self, key: u8) -> Option<&mut T> {
        self.keys[..self.len as usize]
            .iter()
            .position(|&k| k == key)
            .map(|idx| {
                // SAFETY: Children at index less than `len` must have been initialized.
                unsafe { self.children[idx].assume_init_mut() }
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
    fn is_full(&self) -> bool {
        self.len as usize >= N
    }

    fn add_child(&mut self, key: u8, child: T) {
        debug_assert!((self.len as usize) < N);
        self.indices[key as usize] = Some(self.len);
        self.children[self.len as usize].write(child);
        self.len += 1;
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

#[derive(Debug)]
pub struct IndirectIter<'a, T, const N: usize> {
    indices: &'a Indirect<T, N>,
    idx: usize,
}

impl<'a, T, const N: usize> Iterator for IndirectIter<'a, T, N> {
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

#[derive(Debug)]
pub struct Direct<T> {
    children: [Option<T>; 256],
}

impl<T> Default for Direct<T> {
    fn default() -> Self {
        Self {
            children: [Self::DEFAULT_CHILD; 256],
        }
    }
}

impl<T> Indices<T> for Direct<T> {
    fn is_full(&self) -> bool {
        false
    }

    fn add_child(&mut self, key: u8, child: T) {
        self.children[key as usize] = Some(child);
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
        }
        assert!(indices.is_full());
    }

    #[test]
    fn test_sorted_indices_get_child() {
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
        }
        assert!(!indices.is_full());
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
}
