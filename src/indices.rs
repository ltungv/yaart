mod indices16;
mod indices256;
mod indices4;
mod indices48;

pub use indices16::*;
pub use indices256::*;
pub use indices4::*;
pub use indices48::*;

/// A trait implemented by data structure that can be used as indices in an Adaptive Radix Tree.
pub trait Indices<T> {
    /// Returns the number of children currently in the indices.
    fn len(&self) -> usize;

    /// Returns `true` if the number of children reaches the maximum capacity.
    fn is_full(&self) -> bool;

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

#[cfg(test)]
mod tests {
    use crate::indices::Indices;

    use super::{
        indices16::Indices16, indices256::Indices256, indices4::Indices4, indices48::Indices48,
    };

    fn test_indices_add_child<IDX>(indices: &mut IDX, max: u8)
    where
        IDX: Indices<usize>,
    {
        for i in 0..=max {
            indices.add_child(i, i as usize);
            assert_eq!(indices.len(), i as usize + 1);
        }
        assert!(indices.is_full());
    }

    fn test_indices_del_child<IDX>(indices: &mut IDX, max: u8)
    where
        IDX: Indices<usize>,
    {
        for i in 0..=max {
            let child = indices.del_child(i);
            assert!(child.is_none());
        }
        for i in 0..=max {
            indices.add_child(i, i as usize);
        }
        for i in 0..=max {
            let child = indices.del_child(i);
            assert_eq!(child, Some(i as usize));
            let child = indices.child_ref(i);
            assert!(child.is_none());
        }
        assert_eq!(indices.len(), 0);
    }

    fn test_indices_child_ref<IDX>(indices: &mut IDX, max: u8)
    where
        IDX: Indices<usize>,
    {
        for i in 0..=max {
            let child = indices.child_ref(i);
            assert!(child.is_none());
        }
        for i in 0..=max {
            indices.add_child(i, i as usize);
        }
        for i in 0..=max {
            let child = indices.child_ref(i);
            assert_eq!(child, Some(&(i as usize)));
        }
    }

    fn test_indices_child_mut<IDX>(indices: &mut IDX, max: u8)
    where
        IDX: Indices<usize>,
    {
        for i in 0..=max {
            let child = indices.child_mut(i);
            assert!(child.is_none());
        }
        for i in 0..=max {
            indices.add_child(i, i as usize);
        }
        for i in 0..=max {
            let child = indices.child_mut(i).expect("child must exist");
            *child = (max - i) as usize;
        }
        for i in 0..=max {
            let child = indices.child_ref(i);
            assert_eq!(child, Some(&((max - i) as usize)));
        }
    }

    fn test_indices_min<IDX>(indices: &mut IDX, max: u8)
    where
        IDX: Indices<usize>,
    {
        for i in (0..=max).rev() {
            indices.add_child(i, i as usize);
            let min_child = indices.min();
            assert_eq!(min_child, Some(&(i as usize)));
        }
    }

    fn test_indices_max<IDX>(indices: &mut IDX, max: u8)
    where
        IDX: Indices<usize>,
    {
        for i in 0..=max {
            indices.add_child(i, i as usize);
            let max_child = indices.max();
            assert_eq!(max_child, Some(&(i as usize)));
        }
    }

    fn test_indices_iter<'a, IDX>(indices: &'a mut IDX, max: u8)
    where
        IDX: Indices<usize>,
        &'a IDX: IntoIterator<Item = (u8, &'a usize)>,
    {
        for i in (0..=max).rev() {
            indices.add_child(i, i as usize);
        }
        for (i, (key, child)) in indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_all_indices_add_child() {
        let mut indices = Indices4::<usize>::default();
        test_indices_add_child(&mut indices, 3);

        let mut indices = Indices16::<usize>::default();
        test_indices_add_child(&mut indices, 15);

        let mut indices = Indices48::<usize>::default();
        test_indices_add_child(&mut indices, 47);

        let mut indices = Indices256::<usize>::default();
        test_indices_add_child(&mut indices, 255);
    }

    #[test]
    fn test_all_indices_del_child() {
        let mut indices = Indices4::<usize>::default();
        test_indices_del_child(&mut indices, 3);

        let mut indices = Indices16::<usize>::default();
        test_indices_del_child(&mut indices, 15);

        let mut indices = Indices48::<usize>::default();
        test_indices_del_child(&mut indices, 47);

        let mut indices = Indices256::<usize>::default();
        test_indices_del_child(&mut indices, 255);
    }

    #[test]
    fn test_all_indices_child_ref() {
        let mut indices = Indices4::<usize>::default();
        test_indices_child_ref(&mut indices, 3);

        let mut indices = Indices16::<usize>::default();
        test_indices_child_ref(&mut indices, 15);

        let mut indices = Indices48::<usize>::default();
        test_indices_child_ref(&mut indices, 47);

        let mut indices = Indices256::<usize>::default();
        test_indices_child_ref(&mut indices, 255);
    }

    #[test]
    fn test_all_indices_child_mut() {
        let mut indices = Indices4::<usize>::default();
        test_indices_child_mut(&mut indices, 3);

        let mut indices = Indices16::<usize>::default();
        test_indices_child_mut(&mut indices, 15);

        let mut indices = Indices48::<usize>::default();
        test_indices_child_mut(&mut indices, 47);

        let mut indices = Indices256::<usize>::default();
        test_indices_child_mut(&mut indices, 255);
    }

    #[test]
    fn test_all_indices_min() {
        let mut indices = Indices4::<usize>::default();
        test_indices_min(&mut indices, 3);

        let mut indices = Indices16::<usize>::default();
        test_indices_min(&mut indices, 15);

        let mut indices = Indices48::<usize>::default();
        test_indices_min(&mut indices, 47);

        let mut indices = Indices256::<usize>::default();
        test_indices_min(&mut indices, 255);
    }

    #[test]
    fn test_all_indices_max() {
        let mut indices = Indices4::<usize>::default();
        test_indices_max(&mut indices, 3);

        let mut indices = Indices16::<usize>::default();
        test_indices_max(&mut indices, 15);

        let mut indices = Indices48::<usize>::default();
        test_indices_max(&mut indices, 47);

        let mut indices = Indices256::<usize>::default();
        test_indices_max(&mut indices, 255);
    }

    #[test]
    fn test_all_indices_iter() {
        let mut indices = Indices4::<usize>::default();
        test_indices_iter(&mut indices, 3);

        let mut indices = Indices16::<usize>::default();
        test_indices_iter(&mut indices, 15);

        let mut indices = Indices48::<usize>::default();
        test_indices_iter(&mut indices, 47);

        let mut indices = Indices256::<usize>::default();
        test_indices_iter(&mut indices, 255);
    }

    #[test]
    fn test_indices4_from_indices16() {
        let mut indices16 = Indices16::<usize>::default();
        for i in 0..=3 {
            indices16.add_child(i, i as usize);
        }
        let indices4 = Indices4::from(&mut indices16);
        assert_eq!(indices4.len(), 4);
        for i in 0..=3 {
            let child = indices4.child_ref(i);
            assert_eq!(child, Some(&(i as usize)));
        }
        assert_eq!(indices16.len(), 0);
        for key in 0..=255 {
            let child = indices16.child_ref(key);
            assert_eq!(child, None);
        }
    }

    #[test]
    fn test_indices16_from_indices4() {
        let mut indices4 = Indices4::<usize>::default();
        for i in 0..=3 {
            indices4.add_child(i, i as usize);
        }
        let indices16 = Indices16::from(&mut indices4);
        assert_eq!(indices16.len(), 4);
        for i in 0..=3 {
            let child = indices16.child_ref(i);
            assert_eq!(child, Some(&(i as usize)));
        }
        assert_eq!(indices4.len(), 0);
        for key in 0..=255 {
            let child = indices4.child_ref(key);
            assert_eq!(child, None);
        }
    }

    #[test]
    fn test_indices16_from_indices48() {
        let mut indices48 = Indices48::<usize>::default();
        for i in 0..=15 {
            indices48.add_child(i, i as usize);
        }
        let indices16 = Indices16::from(&mut indices48);
        assert_eq!(indices16.len(), 16);
        for i in 0..=15 {
            let child = indices16.child_ref(i);
            assert_eq!(child, Some(&(i as usize)));
        }
        assert_eq!(indices48.len(), 0);
        for key in 0..=255 {
            let child = indices48.child_ref(key);
            assert_eq!(child, None);
        }
    }

    #[test]
    fn test_indices48_from_indices16() {
        let mut indices16 = Indices16::<usize>::default();
        for i in 0..=15 {
            indices16.add_child(i, i as usize);
        }
        let indices48 = Indices48::from(&mut indices16);
        assert_eq!(indices48.len(), 16);
        for i in 0..=15 {
            let child = indices48.child_ref(i);
            assert_eq!(child, Some(&(i as usize)));
        }
        assert_eq!(indices16.len(), 0);
        for key in 0..=255 {
            let child = indices16.child_ref(key);
            assert_eq!(child, None);
        }
    }

    #[test]
    fn test_indices48_from_indices256() {
        let mut indices256 = Indices256::<usize>::default();
        for i in 0..=47 {
            indices256.add_child(i, i as usize);
        }
        let indices48 = Indices48::from(&mut indices256);
        assert_eq!(indices48.len(), 48);
        for i in 0..=47 {
            let child = indices48.child_ref(i);
            assert_eq!(child, Some(&(i as usize)));
        }
        assert_eq!(indices256.len(), 0);
        for key in 0..=255 {
            let child = indices256.child_ref(key);
            assert_eq!(child, None);
        }
    }

    #[test]
    fn test_indices256_from_indices48() {
        let mut indices48 = Indices48::<usize>::default();
        for i in 0..=47 {
            indices48.add_child(i, i as usize);
        }
        let indices256 = Indices256::from(&mut indices48);
        assert_eq!(indices256.len(), 48);
        for i in 0..=47 {
            let child = indices256.child_ref(i);
            assert_eq!(child, Some(&(i as usize)));
        }
        assert_eq!(indices48.len(), 0);
        for key in 0..=255 {
            let child = indices48.child_ref(key);
            assert_eq!(child, None);
        }
    }
}
