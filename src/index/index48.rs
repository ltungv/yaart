use super::{Index, Index16, Index256};

/// A data structure for holding index that uses 2 arrays of the same size to map from byte keys
/// to their children. The keys and pointers are stored at corresponding positions and the keys are
/// sorted.
#[derive(Debug)]
pub struct Index48<T> {
    pub(super) len: u8,
    pub(super) keys: [u8; 256],
    pub(super) children: [Option<T>; 48],
}

impl<T> Index48<T> {
    const fn index_of_key(&self, key: u8) -> Option<usize> {
        let idx = self.keys[key as usize];
        if idx == 0 {
            return None;
        }
        Some((idx - 1) as usize)
    }
}

impl<T> Default for Index48<T> {
    fn default() -> Self {
        Self {
            len: 0,
            keys: [0; 256],
            children: [const { None }; 48],
        }
    }
}

impl<'a, T> IntoIterator for &'a Index48<T> {
    type Item = (u8, &'a T);

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            index: self,
            key: 0,
        }
    }
}

impl<T> Index<T> for Index48<T> {
    fn len(&self) -> usize {
        self.len as usize
    }

    fn del_child(&mut self, key: u8) -> Option<T> {
        self.index_of_key(key).map(|idx| {
            self.len -= 1;
            self.keys[key as usize] = 0;
            self.children[idx].take().expect("child must exist")
        })
    }

    fn add_child(&mut self, key: u8, child: T) {
        for idx in 0u8..48u8 {
            if self.children[idx as usize].is_none() {
                self.len += 1;
                self.keys[key as usize] = idx + 1;
                self.children[idx as usize] = Some(child);
                break;
            }
        }
    }

    fn child_ref(&self, key: u8) -> Option<&T> {
        self.index_of_key(key)
            .map(|idx| self.children[idx].as_ref().expect("child must exist"))
    }

    fn child_mut(&mut self, key: u8) -> Option<&mut T> {
        self.index_of_key(key)
            .map(|idx| self.children[idx].as_mut().expect("child must exist"))
    }

    fn min(&self) -> Option<&T> {
        self.keys.iter().find(|&&idx| idx > 0).map(|&idx| {
            self.children[idx as usize - 1]
                .as_ref()
                .expect("child must exist")
        })
    }

    fn max(&self) -> Option<&T> {
        self.keys.iter().rev().find(|&&idx| idx > 0).map(|&idx| {
            self.children[idx as usize - 1]
                .as_ref()
                .expect("child must exist")
        })
    }
}

impl<T> From<&mut Index16<T>> for Index48<T> {
    fn from(other: &mut Index16<T>) -> Self {
        let mut index = Self::default();
        for idx in 0..other.len {
            let key = other.keys[idx as usize];
            let child = other.children[idx as usize].take();
            index.keys[key as usize] = idx + 1;
            index.children[idx as usize] = child;
        }
        index.len = other.len;
        other.len = 0;
        index
    }
}

impl<T> From<&mut Index256<T>> for Index48<T> {
    fn from(other: &mut Index256<T>) -> Self {
        let mut index = Self::default();
        for key in 0..=255 {
            let child = other.children[key].take();
            if let Some(child) = child {
                index.keys[key] = index.len + 1;
                index.children[index.len as usize] = Some(child);
                index.len += 1;
            }
        }
        other.len = 0;
        index
    }
}

/// An iterator over the index and their children.
#[derive(Debug)]
pub struct Iter<'a, T> {
    index: &'a Index48<T>,
    key: u16,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (u8, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let key = u8::try_from(self.key).ok()?;
            self.key += 1;
            if let Some(child) = &self.index.child_ref(key) {
                return Some((key, child));
            }
        }
    }
}
