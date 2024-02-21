use std::mem::MaybeUninit;

use super::{make_uninitialized_array, take_uninit, Indices, Indirect};

/// A data structure for holding indices in sorted order. This is used when the number of children is
/// small enough such that we can do search by comparison without affecting the performance.
#[derive(Debug)]
pub struct Sorted<T, const N: usize> {
    pub(super) len: u8,
    pub(super) keys: [u8; N],
    pub(super) children: [MaybeUninit<T>; N],
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
        self.len as usize >= N
    }

    fn del_child(&mut self, key: u8) -> Option<T> {
        if N > 4 {
            self.search_binary(key)
        } else {
            self.search_linear(key)
        }
        .map(|idx| {
            // SAFETY: Children at index less than `len` must have been initialized.
            let child = unsafe { take_uninit(&mut self.children[idx]) };
            self.len -= 1;
            self.keys[idx..].rotate_left(1);
            self.children[idx..].rotate_left(1);
            child
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
            let mut i = 0;
            while i < self.len as usize && self.keys[i] < key {
                i += 1;
            }
            i
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
        .map(|idx| {
            // SAFETY: Children at index less than `len` must have been initialized.
            unsafe { self.children[idx].assume_init_ref() }
        })
    }

    fn child_mut(&mut self, key: u8) -> Option<&mut T> {
        if N > 4 {
            self.search_binary(key)
        } else {
            self.search_linear(key)
        }
        .map(|idx| {
            // SAFETY: Children at index less than `len` must have been initialized.
            unsafe { self.children[idx].assume_init_mut() }
        })
    }

    fn min(&self) -> Option<&T> {
        self.children[..self.len as usize].first().map(|child| {
            // SAFETY: Children at index less than `len` must have been initialized.
            unsafe { child.assume_init_ref() }
        })
    }

    fn max(&self) -> Option<&T> {
        self.children[..self.len as usize].last().map(|child| {
            // SAFETY: Children at index less than `len` must have been initialized.
            unsafe { child.assume_init_ref() }
        })
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a Sorted<T, N> {
    type Item = (u8, &'a T);

    type IntoIter = Iter<'a, T, N>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            indices: self,
            idx: 0,
        }
    }
}

impl<T, const N: usize> Sorted<T, N> {
    pub fn release(&mut self) -> Option<(u8, T)> {
        if self.len != 1 {
            return None;
        }
        let key = self.keys[0];
        // SAFETY: Children at index less than `len` must have been initialized.
        let child = unsafe { take_uninit(&mut self.children[0]) };
        self.len -= 1;
        self.keys.rotate_left(1);
        self.children.rotate_left(1);
        Some((key, child))
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
            if let Some(idx_old) = other.indices[key as usize] {
                let idx_new = self.len as usize;
                self.len += 1;
                self.keys[idx_new] = key;
                std::mem::swap(
                    &mut self.children[idx_new],
                    &mut other.children[idx_old as usize],
                );
            }
        }
        other.len = 0;
    }

    const fn search_linear(&self, key: u8) -> Option<usize> {
        let mut i = 0;
        while i < self.len as usize {
            if self.keys[i] == key {
                return Some(i);
            }
            i += 1;
        }
        None
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
pub struct Iter<'a, T, const N: usize> {
    indices: &'a Sorted<T, N>,
    idx: usize,
}

impl<'a, T, const N: usize> Iterator for Iter<'a, T, N> {
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
