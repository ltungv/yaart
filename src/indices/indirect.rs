use std::mem::MaybeUninit;

use super::{make_uninitialized_array, Direct, Indices, Sorted};

#[derive(Debug)]
pub struct Indirect<T, const N: usize> {
    pub(super) len: u8,
    pub(super) indices: [Option<u8>; 256],
    pub(super) children: [MaybeUninit<T>; N],
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

    type IntoIter = Iter<'a, T, N>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
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
pub struct Iter<'a, T, const N: usize> {
    indices: &'a Indirect<T, N>,
    idx: usize,
}

impl<'a, T, const N: usize> Iterator for Iter<'a, T, N> {
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
