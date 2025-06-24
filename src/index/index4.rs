use super::{ordered_insert, ordered_remove, Index, Index16};

#[derive(Debug)]
pub struct Index4<T> {
    pub(super) len: u8,
    pub(super) keys: [u8; 4],
    pub(super) children: [Option<T>; 4],
}

impl<T> Index4<T> {
    pub fn free(&mut self) -> (u8, T) {
        self.len -= 1;
        let key = ordered_remove(&mut self.keys, 0);
        let child = ordered_remove(&mut self.children, 0)
            .take()
            .expect("child must exist");
        (*key, child)
    }

    fn index_of_key(&self, key: u8) -> Option<usize> {
        self.keys[..self.len as usize]
            .iter()
            .position(|&k| k == key)
    }
}

impl<T> Default for Index4<T> {
    fn default() -> Self {
        Self {
            len: 0,
            keys: [0; 4],
            children: [const { None }; 4],
        }
    }
}

impl<'a, T> IntoIterator for &'a Index4<T> {
    type Item = (u8, &'a T);

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            index: self,
            idx: 0,
        }
    }
}

impl<T> Index<T> for Index4<T> {
    fn len(&self) -> usize {
        self.len as usize
    }

    fn del_child(&mut self, key: u8) -> Option<T> {
        self.index_of_key(key).map(|idx| {
            self.len -= 1;
            ordered_remove(&mut self.keys, idx);
            ordered_remove(&mut self.children, idx)
                .take()
                .expect("child must exist")
        })
    }

    fn add_child(&mut self, key: u8, child: T) {
        let mut idx = 0;
        while idx < self.len as usize && self.keys[idx] < key {
            idx += 1;
        }
        self.len += 1;
        ordered_insert(&mut self.keys, idx, key);
        ordered_insert(&mut self.children, idx, Some(child));
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
        self.children[..self.len as usize]
            .first()
            .map(|child| child.as_ref().expect("child must exist"))
    }

    fn max(&self) -> Option<&T> {
        self.children[..self.len as usize]
            .last()
            .map(|child| child.as_ref().expect("child must exist"))
    }
}

impl<T> From<&mut Index16<T>> for Index4<T> {
    fn from(other: &mut Index16<T>) -> Self {
        let mut index = Self::default();
        for i in 0..other.len as usize {
            index.keys[i] = other.keys[i];
            index.children[i] = other.children[i].take();
        }
        index.len = other.len;
        other.len = 0;
        index
    }
}

/// An iterator over the index and their children.
#[derive(Debug)]
pub struct Iter<'a, T> {
    index: &'a Index4<T>,
    idx: u8,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (u8, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.index.len {
            return None;
        }
        let key = self.index.keys[self.idx as usize];
        let child = self.index.children[self.idx as usize]
            .as_ref()
            .expect("child must exist");
        self.idx += 1;
        Some((key, child))
    }
}
