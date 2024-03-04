use super::Indices;

/// A data structure for holding indices that uses 2 arrays of the same size to map from byte keys
/// to their children. The keys and pointers are stored at corresponding positions and the keys are
/// sorted.
#[derive(Debug)]
pub struct Indices256<T> {
    pub len: u16,
    pub children: [Option<Box<T>>; 256],
}

impl<T> Indices256<T> {
    const NONE: Option<Box<T>> = None;
}

impl<T> Default for Indices256<T> {
    fn default() -> Self {
        Self {
            len: 0,
            children: [Self::NONE; 256],
        }
    }
}

impl<'a, T> IntoIterator for &'a Indices256<T> {
    type Item = (u8, &'a T);

    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        Iter {
            indices: self,
            key: 0,
        }
    }
}

impl<T> Indices<T> for Indices256<T> {
    fn len(&self) -> usize {
        self.len as usize
    }

    fn is_full(&self) -> bool {
        self.len as usize >= 256
    }

    fn del_child(&mut self, key: u8) -> Option<T> {
        self.children[key as usize].take().map(|child| {
            self.len -= 1;
            *child
        })
    }

    fn add_child(&mut self, key: u8, child: T) {
        if self.children[key as usize]
            .replace(Box::new(child))
            .is_none()
        {
            self.len += 1;
        }
    }

    fn child_ref(&self, key: u8) -> Option<&T> {
        self.children[key as usize].as_ref().map(Box::as_ref)
    }

    fn child_mut(&mut self, key: u8) -> Option<&mut T> {
        self.children[key as usize].as_mut().map(Box::as_mut)
    }

    fn min(&self) -> Option<&T> {
        self.children
            .iter()
            .find_map(|child| child.as_ref().map(Box::as_ref))
    }

    fn max(&self) -> Option<&T> {
        self.children
            .iter()
            .rev()
            .find_map(|child| child.as_ref().map(Box::as_ref))
    }
}

/// An iterator over the indices and their children.
#[derive(Debug)]
pub struct Iter<'a, T> {
    indices: &'a Indices256<T>,
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
