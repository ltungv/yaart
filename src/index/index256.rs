use super::{Index, Index48};

/// A data structure for holding index that uses 2 arrays of the same size to map from byte keys
/// to their children. The keys and pointers are stored at corresponding positions and the keys are
/// sorted.
#[derive(Debug)]
pub struct Index256<T> {
    pub(super) len: u16,
    pub(super) children: [Option<T>; 256],
}

impl<T> Default for Index256<T> {
    fn default() -> Self {
        Self {
            len: 0,
            children: [const { None }; 256],
        }
    }
}

impl<'a, T> IntoIterator for &'a Index256<T> {
    type Item = (u8, &'a T);

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            index: self,
            key: 0,
        }
    }
}

impl<T> Index<T> for Index256<T> {
    fn len(&self) -> usize {
        self.len as usize
    }

    fn del_child(&mut self, key: u8) -> Option<T> {
        self.children[key as usize]
            .take()
            .inspect(|_| self.len -= 1)
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
        self.children.iter().find_map(|child| child.as_ref())
    }

    fn max(&self) -> Option<&T> {
        self.children.iter().rev().find_map(|child| child.as_ref())
    }
}

impl<T> From<&mut Index48<T>> for Index256<T> {
    fn from(other: &mut Index48<T>) -> Self {
        let mut index = Self::default();
        for key in 0..=255 {
            let idx_old = other.keys[key];
            if idx_old == 0 {
                continue;
            }
            other.keys[key] = 0;
            let child = other.children[idx_old as usize - 1].take();
            index.children[key] = child;
        }
        index.len = u16::from(other.len);
        other.len = 0;
        index
    }
}

/// An iterator over the index and their children.
#[derive(Debug)]
pub struct Iter<'a, T> {
    index: &'a Index256<T>,
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
