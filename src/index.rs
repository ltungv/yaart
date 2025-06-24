mod index16;
mod index256;
mod index4;
mod index48;

pub use index16::*;
pub use index256::*;
pub use index4::*;
pub use index48::*;

/// A trait implemented by data structure that can be used as index in an Adaptive Radix Tree.
pub trait Index<T> {
    /// Returns the number of children currently in the index.
    fn len(&self) -> usize;

    /// Removes the child associated to the given key and returns it.
    fn del_child(&mut self, key: u8) -> Option<T>;

    /// Adds a child associated with the given key.
    fn add_child(&mut self, key: u8, child: T);

    /// Returns a shared reference to the child associated to the given key.
    fn child_ref(&self, key: u8) -> Option<&T>;

    /// Returns a mutable reference to the child associated to the given key.
    fn child_mut(&mut self, key: u8) -> Option<&mut T>;

    /// Returns a shared reference to the child associated with the minimum key.
    fn min(&self) -> Option<&T>;

    /// Returns a shared reference to the child associated with the maximum key.
    fn max(&self) -> Option<&T>;
}

fn ordered_insert<T>(items: &mut [T], index: usize, value: T) {
    items[index..].rotate_right(1);
    items[index] = value;
}

fn ordered_remove<T>(items: &mut [T], index: usize) -> &mut T {
    items[index..].rotate_left(1);
    &mut items[items.len() - 1]
}

#[cfg(test)]
mod tests {
    use crate::index::Index;

    use super::{index16::Index16, index256::Index256, index4::Index4, index48::Index48};

    fn test_index_add_child<IDX>(index: &mut IDX, max: u8)
    where
        IDX: Index<usize>,
    {
        for i in 0..=max {
            index.add_child(i, i as usize);
            assert_eq!(index.len(), i as usize + 1);
        }
    }

    fn test_index_del_child<IDX>(index: &mut IDX, max: u8)
    where
        IDX: Index<usize>,
    {
        for i in 0..=max {
            let child = index.del_child(i);
            assert!(child.is_none());
        }
        for i in 0..=max {
            index.add_child(i, i as usize);
        }
        for i in 0..=max {
            let child = index.del_child(i);
            assert_eq!(child, Some(i as usize));
            let child = index.child_ref(i);
            assert!(child.is_none());
        }
        assert_eq!(index.len(), 0);
    }

    fn test_index_child_ref<IDX>(index: &mut IDX, max: u8)
    where
        IDX: Index<usize>,
    {
        for i in 0..=max {
            let child = index.child_ref(i);
            assert!(child.is_none());
        }
        for i in 0..=max {
            index.add_child(i, i as usize);
        }
        for i in 0..=max {
            let child = index.child_ref(i);
            assert_eq!(child, Some(&(i as usize)));
        }
    }

    fn test_index_child_mut<IDX>(index: &mut IDX, max: u8)
    where
        IDX: Index<usize>,
    {
        for i in 0..=max {
            let child = index.child_mut(i);
            assert!(child.is_none());
        }
        for i in 0..=max {
            index.add_child(i, i as usize);
        }
        for i in 0..=max {
            let child = index.child_mut(i).expect("child must exist");
            *child = (max - i) as usize;
        }
        for i in 0..=max {
            let child = index.child_ref(i);
            assert_eq!(child, Some(&((max - i) as usize)));
        }
    }

    fn test_index_min<IDX>(index: &mut IDX, max: u8)
    where
        IDX: Index<usize>,
    {
        for i in (0..=max).rev() {
            index.add_child(i, i as usize);
            let min_child = index.min();
            assert_eq!(min_child, Some(&(i as usize)));
        }
    }

    fn test_index_max<IDX>(index: &mut IDX, max: u8)
    where
        IDX: Index<usize>,
    {
        for i in 0..=max {
            index.add_child(i, i as usize);
            let max_child = index.max();
            assert_eq!(max_child, Some(&(i as usize)));
        }
    }

    fn test_index_iter<'a, IDX>(index: &'a mut IDX, max: u8)
    where
        IDX: Index<usize>,
        &'a IDX: IntoIterator<Item = (u8, &'a usize)>,
    {
        for i in (0..=max).rev() {
            index.add_child(i, i as usize);
        }
        for (i, (key, child)) in index.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_all_index_add_child() {
        let mut index = Index4::<usize>::default();
        test_index_add_child(&mut index, 3);

        let mut index = Index16::<usize>::default();
        test_index_add_child(&mut index, 15);

        let mut index = Index48::<usize>::default();
        test_index_add_child(&mut index, 47);

        let mut index = Index256::<usize>::default();
        test_index_add_child(&mut index, 255);
    }

    #[test]
    fn test_all_index_del_child() {
        let mut index = Index4::<usize>::default();
        test_index_del_child(&mut index, 3);

        let mut index = Index16::<usize>::default();
        test_index_del_child(&mut index, 15);

        let mut index = Index48::<usize>::default();
        test_index_del_child(&mut index, 47);

        let mut index = Index256::<usize>::default();
        test_index_del_child(&mut index, 255);
    }

    #[test]
    fn test_all_index_child_ref() {
        let mut index = Index4::<usize>::default();
        test_index_child_ref(&mut index, 3);

        let mut index = Index16::<usize>::default();
        test_index_child_ref(&mut index, 15);

        let mut index = Index48::<usize>::default();
        test_index_child_ref(&mut index, 47);

        let mut index = Index256::<usize>::default();
        test_index_child_ref(&mut index, 255);
    }

    #[test]
    fn test_all_index_child_mut() {
        let mut index = Index4::<usize>::default();
        test_index_child_mut(&mut index, 3);

        let mut index = Index16::<usize>::default();
        test_index_child_mut(&mut index, 15);

        let mut index = Index48::<usize>::default();
        test_index_child_mut(&mut index, 47);

        let mut index = Index256::<usize>::default();
        test_index_child_mut(&mut index, 255);
    }

    #[test]
    fn test_all_index_min() {
        let mut index = Index4::<usize>::default();
        test_index_min(&mut index, 3);

        let mut index = Index16::<usize>::default();
        test_index_min(&mut index, 15);

        let mut index = Index48::<usize>::default();
        test_index_min(&mut index, 47);

        let mut index = Index256::<usize>::default();
        test_index_min(&mut index, 255);
    }

    #[test]
    fn test_all_index_max() {
        let mut index = Index4::<usize>::default();
        test_index_max(&mut index, 3);

        let mut index = Index16::<usize>::default();
        test_index_max(&mut index, 15);

        let mut index = Index48::<usize>::default();
        test_index_max(&mut index, 47);

        let mut index = Index256::<usize>::default();
        test_index_max(&mut index, 255);
    }

    #[test]
    fn test_all_index_iter() {
        let mut index = Index4::<usize>::default();
        test_index_iter(&mut index, 3);

        let mut index = Index16::<usize>::default();
        test_index_iter(&mut index, 15);

        let mut index = Index48::<usize>::default();
        test_index_iter(&mut index, 47);

        let mut index = Index256::<usize>::default();
        test_index_iter(&mut index, 255);
    }

    #[test]
    fn test_index4_from_index16() {
        let mut index16 = Index16::<usize>::default();
        for i in 0..=3 {
            index16.add_child(i, i as usize);
        }
        let index4 = Index4::from(&mut index16);
        assert_eq!(index4.len(), 4);
        for i in 0..=3 {
            let child = index4.child_ref(i);
            assert_eq!(child, Some(&(i as usize)));
        }
        assert_eq!(index16.len(), 0);
        for key in 0..=255 {
            let child = index16.child_ref(key);
            assert_eq!(child, None);
        }
    }

    #[test]
    fn test_index16_from_index4() {
        let mut index4 = Index4::<usize>::default();
        for i in 0..=3 {
            index4.add_child(i, i as usize);
        }
        let index16 = Index16::from(&mut index4);
        assert_eq!(index16.len(), 4);
        for i in 0..=3 {
            let child = index16.child_ref(i);
            assert_eq!(child, Some(&(i as usize)));
        }
        assert_eq!(index4.len(), 0);
        for key in 0..=255 {
            let child = index4.child_ref(key);
            assert_eq!(child, None);
        }
    }

    #[test]
    fn test_index16_from_index48() {
        let mut index48 = Index48::<usize>::default();
        for i in 0..=15 {
            index48.add_child(i, i as usize);
        }
        let index16 = Index16::from(&mut index48);
        assert_eq!(index16.len(), 16);
        for i in 0..=15 {
            let child = index16.child_ref(i);
            assert_eq!(child, Some(&(i as usize)));
        }
        assert_eq!(index48.len(), 0);
        for key in 0..=255 {
            let child = index48.child_ref(key);
            assert_eq!(child, None);
        }
    }

    #[test]
    fn test_index48_from_index16() {
        let mut index16 = Index16::<usize>::default();
        for i in 0..=15 {
            index16.add_child(i, i as usize);
        }
        let index48 = Index48::from(&mut index16);
        assert_eq!(index48.len(), 16);
        for i in 0..=15 {
            let child = index48.child_ref(i);
            assert_eq!(child, Some(&(i as usize)));
        }
        assert_eq!(index16.len(), 0);
        for key in 0..=255 {
            let child = index16.child_ref(key);
            assert_eq!(child, None);
        }
    }

    #[test]
    fn test_index48_from_index256() {
        let mut index256 = Index256::<usize>::default();
        for i in 0..=47 {
            index256.add_child(i, i as usize);
        }
        let index48 = Index48::from(&mut index256);
        assert_eq!(index48.len(), 48);
        for i in 0..=47 {
            let child = index48.child_ref(i);
            assert_eq!(child, Some(&(i as usize)));
        }
        assert_eq!(index256.len(), 0);
        for key in 0..=255 {
            let child = index256.child_ref(key);
            assert_eq!(child, None);
        }
    }

    #[test]
    fn test_index256_from_index48() {
        let mut index48 = Index48::<usize>::default();
        for i in 0..=47 {
            index48.add_child(i, i as usize);
        }
        let index256 = Index256::from(&mut index48);
        assert_eq!(index256.len(), 48);
        for i in 0..=47 {
            let child = index256.child_ref(i);
            assert_eq!(child, Some(&(i as usize)));
        }
        assert_eq!(index48.len(), 0);
        for key in 0..=255 {
            let child = index48.child_ref(key);
            assert_eq!(child, None);
        }
    }
}
