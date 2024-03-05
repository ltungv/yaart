use super::{Indices, Indices16, Indices256};

/// A data structure for holding indices that uses 2 arrays of the same size to map from byte keys
/// to their children. The keys and pointers are stored at corresponding positions and the keys are
/// sorted.
#[derive(Debug)]
pub struct Indices48<T> {
    pub(super) len: u8,
    pub(super) keys: [u8; 256],
    pub(super) children: [Option<Box<T>>; 48],
}

impl<T> Indices48<T> {
    const NONE: Option<Box<T>> = None;

    const fn index_of_key(&self, key: u8) -> Option<usize> {
        let idx = self.keys[key as usize];
        if idx == 0 {
            return None;
        }
        Some((idx - 1) as usize)
    }
}

impl<T> Default for Indices48<T> {
    fn default() -> Self {
        Self {
            len: 0,
            keys: [0; 256],
            children: [Self::NONE; 48],
        }
    }
}

impl<'a, T> IntoIterator for &'a Indices48<T> {
    type Item = (u8, &'a T);

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            indices: self,
            key: 0,
        }
    }
}

impl<T> Indices<T> for Indices48<T> {
    fn len(&self) -> usize {
        self.len as usize
    }

    fn del_child(&mut self, key: u8) -> Option<T> {
        self.index_of_key(key).map(|idx| {
            self.len -= 1;
            self.keys[key as usize] = 0;
            *self.children[idx].take().expect("child must exist")
        })
    }

    fn add_child(&mut self, key: u8, child: T) {
        for idx in 0u8..48u8 {
            if self.children[idx as usize].is_none() {
                self.len += 1;
                self.keys[key as usize] = idx + 1;
                self.children[idx as usize] = Some(Box::new(child));
                break;
            }
        }
    }

    fn child_ref(&self, key: u8) -> Option<&T> {
        self.index_of_key(key).map(|idx| {
            self.children[idx]
                .as_ref()
                .expect("child must exist")
                .as_ref()
        })
    }

    fn child_mut(&mut self, key: u8) -> Option<&mut T> {
        self.index_of_key(key).map(|idx| {
            self.children[idx]
                .as_mut()
                .expect("child must exist")
                .as_mut()
        })
    }

    fn min(&self) -> Option<&T> {
        self.keys.iter().find(|&&idx| idx > 0).map(|&idx| {
            self.children[idx as usize - 1]
                .as_ref()
                .expect("child must exist")
                .as_ref()
        })
    }

    fn max(&self) -> Option<&T> {
        self.keys.iter().rev().find(|&&idx| idx > 0).map(|&idx| {
            self.children[idx as usize - 1]
                .as_ref()
                .expect("child must exist")
                .as_ref()
        })
    }
}

impl<T> From<&mut Indices16<T>> for Indices48<T> {
    fn from(other: &mut Indices16<T>) -> Self {
        let mut indices = Self::default();
        for idx in 0..other.len {
            let key = other.keys[idx as usize];
            let child = other.children[idx as usize].take();
            indices.keys[key as usize] = idx + 1;
            indices.children[idx as usize] = child;
        }
        indices.len = other.len;
        other.len = 0;
        indices
    }
}

impl<T> From<&mut Indices256<T>> for Indices48<T> {
    fn from(other: &mut Indices256<T>) -> Self {
        let mut indices = Self::default();
        for key in 0..=255 {
            if let Some(child) = other.children[key].take() {
                indices.keys[key] = indices.len + 1;
                indices.children[indices.len as usize] = Some(child);
                indices.len += 1;
            }
        }
        other.len = 0;
        indices
    }
}

/// An iterator over the indices and their children.
#[derive(Debug)]
pub struct Iter<'a, T> {
    indices: &'a Indices48<T>,
    key: u16,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (u8, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let key = u8::try_from(self.key).ok()?;
            self.key += 1;
            if let Some(child) = &self.indices.child_ref(key) {
                return Some((key, child));
            }
        }
    }
}
