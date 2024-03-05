use super::{Indices, Indices16};

#[derive(Debug)]
pub struct Indices4<T> {
    pub(super) len: u8,
    pub(super) keys: [u8; 4],
    pub(super) children: [Option<Box<T>>; 4],
}

impl<T> Indices4<T> {
    const NONE: Option<Box<T>> = None;

    pub fn free(&mut self) -> (u8, T) {
        let key = self.keys[0];
        let child = self.children[0].take().expect("child must exist");
        self.len -= 1;
        self.keys.rotate_left(1);
        self.children.rotate_left(1);
        (key, *child)
    }

    fn index_of_key(&self, key: u8) -> Option<usize> {
        self.keys[..self.len as usize]
            .iter()
            .position(|&k| k == key)
    }
}

impl<T> Default for Indices4<T> {
    fn default() -> Self {
        Self {
            len: 0,
            keys: [0; 4],
            children: [Self::NONE; 4],
        }
    }
}

impl<'a, T> IntoIterator for &'a Indices4<T> {
    type Item = (u8, &'a T);

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            indices: self,
            idx: 0,
        }
    }
}

impl<T> Indices<T> for Indices4<T> {
    fn len(&self) -> usize {
        self.len as usize
    }

    fn is_full(&self) -> bool {
        self.len as usize >= 4
    }

    fn del_child(&mut self, key: u8) -> Option<T> {
        self.index_of_key(key).map(|idx| {
            let child = self.children[idx].take().expect("child must exist");
            self.keys[idx..].rotate_left(1);
            self.children[idx..].rotate_left(1);
            self.len -= 1;
            *child
        })
    }

    fn add_child(&mut self, key: u8, child: T) {
        let mut idx = 0;
        while idx < self.len as usize && self.keys[idx] < key {
            idx += 1;
        }
        self.keys[idx..].rotate_right(1);
        self.keys[idx] = key;
        self.children[idx..].rotate_right(1);
        self.children[idx] = Some(Box::new(child));
        self.len += 1;
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
        self.children[..self.len as usize]
            .first()
            .map(|child| child.as_ref().expect("child must exist").as_ref())
    }

    fn max(&self) -> Option<&T> {
        self.children[..self.len as usize]
            .last()
            .map(|child| child.as_ref().expect("child must exist").as_ref())
    }
}

impl<T> From<&mut Indices16<T>> for Indices4<T> {
    fn from(other: &mut Indices16<T>) -> Self {
        let mut indices = Self::default();
        for i in 0..other.len as usize {
            indices.keys[i] = other.keys[i];
            indices.children[i] = other.children[i].take();
        }
        indices.len = other.len;
        other.len = 0;
        indices
    }
}

/// An iterator over the indices and their children.
#[derive(Debug)]
pub struct Iter<'a, T> {
    indices: &'a Indices4<T>,
    idx: u8,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (u8, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx >= self.indices.len {
            return None;
        }
        let key = self.indices.keys[self.idx as usize];
        let child = self.indices.children[self.idx as usize]
            .as_ref()
            .expect("key must point to some child")
            .as_ref();
        self.idx += 1;
        Some((key, child))
    }
}
