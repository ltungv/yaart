use super::Indices;

/// A data structure for holding indices that uses 2 arrays of the same size to map from byte keys
/// to their children. The keys and pointers are stored at corresponding positions and the keys are
/// sorted.
#[derive(Debug)]
pub struct Indices16<T> {
    pub len: u8,
    pub keys: [u8; 16],
    pub children: [Option<Box<T>>; 16],
}

impl<T> Indices16<T> {
    const NONE: Option<Box<T>> = None;

    fn index_of_key(&self, key: u8) -> Result<usize, usize> {
        self.keys[..self.len as usize].binary_search(&key)
    }
}

impl<T> Default for Indices16<T> {
    fn default() -> Self {
        Self {
            len: 0,
            keys: [0; 16],
            children: [Self::NONE; 16],
        }
    }
}

impl<'a, T> IntoIterator for &'a Indices16<T> {
    type Item = (u8, &'a T);

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            indices: self,
            idx: 0,
        }
    }
}

impl<T> Indices<T> for Indices16<T> {
    fn len(&self) -> usize {
        self.len as usize
    }

    fn is_full(&self) -> bool {
        self.len as usize >= 16
    }

    fn del_child(&mut self, key: u8) -> Option<T> {
        self.index_of_key(key)
            .map(|idx| {
                let child = self.children[idx].take().expect("child must exist");
                self.keys[idx..].rotate_left(1);
                self.children[idx..].rotate_left(1);
                self.len -= 1;
                *child
            })
            .ok()
    }

    fn add_child(&mut self, key: u8, child: T) {
        let idx = self
            .index_of_key(key)
            .unwrap_or_else(std::convert::identity);
        self.keys[idx..].rotate_right(1);
        self.keys[idx] = key;
        self.children[idx..].rotate_right(1);
        self.children[idx] = Some(Box::new(child));
        self.len += 1;
    }

    fn child_ref(&self, key: u8) -> Option<&T> {
        self.index_of_key(key)
            .map(|idx| {
                self.children[idx]
                    .as_ref()
                    .expect("child must exist")
                    .as_ref()
            })
            .ok()
    }

    fn child_mut(&mut self, key: u8) -> Option<&mut T> {
        self.index_of_key(key)
            .map(|idx| {
                self.children[idx]
                    .as_mut()
                    .expect("child must exist")
                    .as_mut()
            })
            .ok()
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

/// An iterator over the indices and their children.
#[derive(Debug)]
pub struct Iter<'a, T> {
    indices: &'a Indices16<T>,
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
