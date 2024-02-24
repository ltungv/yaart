use super::{take_uninit, Indices, Indirect};

/// A data structure for holding indices that uses a single 256-element array to map directly from
/// byte keys to their children.
#[derive(Debug)]
pub struct Direct<T> {
    pub(super) len: u16,
    pub(super) children: [Option<T>; 256],
}

impl<T> Direct<T> {
    const DEFAULT_CHILD: Option<T> = None;

    /// Moves all children and keys from the given indirect indices to this one.
    pub fn consume_indirect<const N: usize>(&mut self, other: &mut Indirect<T, N>) {
        self.len = 0;
        for key in 0..256 {
            self.children[key] = other.indices[key].map(|idx| {
                self.len += 1;
                // SAFETY: If we found Some(index), the corresponding child must have been initialized.
                unsafe { take_uninit(&mut other.children[idx as usize]) }
            });
        }
        other.len = 0;
    }
}

impl<T> Default for Direct<T> {
    fn default() -> Self {
        Self {
            len: 0,
            children: [Self::DEFAULT_CHILD; 256],
        }
    }
}

impl<'a, T> IntoIterator for &'a Direct<T> {
    type Item = (u8, &'a T);

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            indices: self,
            idx: 0,
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

/// An iterator over the indices and their children.
#[derive(Debug)]
pub struct Iter<'a, T> {
    indices: &'a Direct<T>,
    idx: usize,
}

impl<'a, T> Iterator for Iter<'a, T> {
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
