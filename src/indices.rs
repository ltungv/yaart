pub mod direct;
pub mod indirect;
pub mod sorted;

pub use direct::Direct;
pub use indirect::Indirect;
pub use sorted::Sorted;

use std::mem::MaybeUninit;

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

fn make_uninitialized_array<T, const N: usize>() -> [MaybeUninit<T>; N] {
    // SAFETY: calling `assume_init` to convert an uninitialized array
    // into an array of uninitialized items is safe.
    unsafe { MaybeUninit::uninit().assume_init() }
}

/// Takes the value from the given `MaybeUninit` leaving it uninitialized.
///
/// # Safety
///
/// The caller must ensure that the given `MaybeUninit` is initialized.
unsafe fn take_uninit<T>(maybe_uninit: &mut MaybeUninit<T>) -> T {
    let mut tmp = MaybeUninit::uninit();
    std::mem::swap(&mut tmp, maybe_uninit);
    unsafe { tmp.assume_init() }
}

#[cfg(test)]
mod tests {
    use crate::indices::{Direct, Indices, Indirect, Sorted};

    #[test]
    fn test_sorted_indices_set_child() {
        let mut indices = Sorted::<usize, 16>::default();
        for i in 0..16 {
            indices.add_child(i, i as usize);
            assert_eq!(indices.len(), i as usize + 1);
        }
        assert!(indices.is_full());
    }

    #[test]
    fn test_sorted4_indices_get_child() {
        let mut indices = Sorted::<usize, 4>::default();
        for i in 0..4 {
            indices.add_child(i, i as usize);
        }
        for i in 0..4 {
            let child = indices.child_ref(i).unwrap();
            assert_eq!(*child, i as usize);
        }
        assert!(indices.child_ref(4).is_none());
    }

    #[test]
    fn test_sorted16_indices_get_child() {
        let mut indices = Sorted::<usize, 16>::default();
        for i in 0..16 {
            indices.add_child(i, i as usize);
        }
        for i in 0..16 {
            let child = indices.child_ref(i).unwrap();
            assert_eq!(*child, i as usize);
        }
        assert!(indices.child_ref(16).is_none());
    }

    #[test]
    fn test_sorted_indices_min_max_child() {
        let mut indices = Sorted::<usize, 16>::default();
        for i in 0..16 {
            indices.add_child(i, i as usize);
            let min_child = indices.min().unwrap();
            let max_child = indices.max().unwrap();
            assert_eq!(*min_child, 0);
            assert_eq!(*max_child, i as usize);
        }

        let mut indices = Sorted::<usize, 16>::default();
        for i in (0..16).rev() {
            indices.add_child(i, i as usize);
            let min_child = indices.min().unwrap();
            let max_child = indices.max().unwrap();
            assert_eq!(*min_child, i as usize);
            assert_eq!(*max_child, 15);
        }
    }

    #[test]
    fn test_sorted4_indices_del_child() {
        let mut indices = Sorted::<usize, 4>::default();
        for i in 0..4 {
            indices.add_child(i, i as usize);
        }
        for i in (0..2).rev() {
            assert_eq!(indices.del_child(i), Some(i as usize));
        }
        for i in (0..2).rev() {
            assert_eq!(indices.del_child(i), None);
        }
        for (i, (k, x)) in (2..4).zip(&indices) {
            assert_eq!(i, k);
            assert_eq!(i as usize, *x);
        }
        assert!(!indices.is_full());
        assert_eq!(indices.len(), 2);
        assert_eq!(indices.into_iter().count(), 2);
    }

    #[test]
    fn test_sorted16_indices_del_child() {
        let mut indices = Sorted::<usize, 16>::default();
        for i in 0..16 {
            indices.add_child(i, i as usize);
        }
        for i in (0..8).rev() {
            assert_eq!(indices.del_child(i), Some(i as usize));
        }
        for i in (0..8).rev() {
            assert_eq!(indices.del_child(i), None);
        }
        for (i, (k, x)) in (8..16).zip(&indices) {
            assert_eq!(i, k);
            assert_eq!(i as usize, *x);
        }
        assert!(!indices.is_full());
        assert_eq!(indices.len(), 8);
        assert_eq!(indices.into_iter().count(), 8);
    }

    #[test]
    fn test_sorted_indices_iter() {
        let mut indices = Sorted::<usize, 16>::default();
        for i in 0..8 {
            indices.add_child(i, i as usize);
        }
        for (i, (key, child)) in indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_indirect_indices_set_child() {
        let mut indices = Indirect::<usize, 48>::default();
        for i in 0..48 {
            indices.add_child(i, i as usize);
            assert_eq!(indices.len(), i as usize + 1);
        }
        assert!(indices.is_full());
    }

    #[test]
    fn test_indirect_indices_get_child() {
        let mut indices = Indirect::<usize, 48>::default();
        for i in 0..48 {
            indices.add_child(i, i as usize);
        }
        for i in 0..48 {
            let child = indices.child_ref(i).unwrap();
            assert_eq!(*child, i as usize);
        }
        assert!(indices.child_ref(48).is_none());
    }

    #[test]
    fn test_indirect_indices_min_max_child() {
        let mut indices = Indirect::<usize, 48>::default();
        for i in 0..48 {
            indices.add_child(i, i as usize);
            let min_child = indices.min().unwrap();
            let max_child = indices.max().unwrap();
            assert_eq!(*min_child, 0);
            assert_eq!(*max_child, i as usize);
        }

        let mut indices = Indirect::<usize, 48>::default();
        for i in (0..48).rev() {
            indices.add_child(i, i as usize);
            let min_child = indices.min().unwrap();
            let max_child = indices.max().unwrap();
            assert_eq!(*min_child, i as usize);
            assert_eq!(*max_child, 47);
        }
    }

    #[test]
    fn test_indirect_indices_del_child() {
        let mut indices = Indirect::<usize, 48>::default();
        for i in 0..48 {
            indices.add_child(i, i as usize);
        }
        for i in (0..24).rev() {
            assert_eq!(indices.del_child(i), Some(i as usize));
        }
        for i in (0..24).rev() {
            assert_eq!(indices.del_child(i), None);
        }
        for (i, (k, x)) in (24..48).zip(&indices) {
            assert_eq!(i, k);
            assert_eq!(i as usize, *x);
        }
        assert!(!indices.is_full());
        assert_eq!(indices.len(), 24);
        assert_eq!(indices.into_iter().count(), 24);
    }

    #[test]
    fn test_indirect_indices_iter() {
        let mut indices = Indirect::<usize, 48>::default();
        for i in 0..24 {
            indices.add_child(i, i as usize);
        }
        for (i, (key, child)) in indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_direct_indices_set_child() {
        let mut indices = Direct::<usize>::default();
        for i in 0..=255 {
            indices.add_child(i, i as usize);
            assert_eq!(indices.len(), i as usize + 1);
        }
        assert!(indices.is_full());
    }

    #[test]
    fn test_direct_indices_get_child() {
        let mut indices = Direct::<usize>::default();
        for i in 0..=255 {
            indices.add_child(i, i as usize);
        }
        for i in 0..=255 {
            let child = indices.child_ref(i).unwrap();
            assert_eq!(*child, i as usize);
        }
    }

    #[test]
    fn test_direct_indices_min_max_child() {
        let mut indices = Direct::<usize>::default();
        for i in 0..=255 {
            indices.add_child(i, i as usize);
            let min_child = indices.min().unwrap();
            let max_child = indices.max().unwrap();
            assert_eq!(*min_child, 0);
            assert_eq!(*max_child, i as usize);
        }

        let mut indices = Direct::<usize>::default();
        for i in (0..=255).rev() {
            indices.add_child(i, i as usize);
            let min_child = indices.min().unwrap();
            let max_child = indices.max().unwrap();
            assert_eq!(*min_child, i as usize);
            assert_eq!(*max_child, 255);
        }
    }

    #[test]
    fn test_direct_indices_del_child() {
        let mut indices = Direct::<usize>::default();
        for i in 0..=255 {
            indices.add_child(i, i as usize);
        }
        for i in (0..128).rev() {
            assert_eq!(indices.del_child(i), Some(i as usize));
        }
        for i in (0..128).rev() {
            assert_eq!(indices.del_child(i), None);
        }
        for (i, (k, x)) in (128..=255).zip(&indices) {
            assert_eq!(i, k);
            assert_eq!(i as usize, *x);
        }
        assert!(!indices.is_full());
        assert_eq!(indices.len(), 128);
        assert_eq!(indices.into_iter().count(), 128);
    }

    #[test]
    fn test_direct_indices_iter() {
        let mut indices = Direct::<usize>::default();
        for i in 0..128 {
            indices.add_child(i, i as usize);
        }
        for (i, (key, child)) in indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_sorted_from_sorted() {
        let mut indices = Sorted::<usize, 4>::default();
        for i in 0..4 {
            indices.add_child(i, i as usize);
        }
        let mut new_indices = Sorted::<usize, 16>::default();
        new_indices.consume_sorted(&mut indices);
        for (i, (key, child)) in new_indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_sorted_from_indirect() {
        let mut indices = Indirect::<usize, 48>::default();
        for i in 0..16 {
            indices.add_child(i, i as usize);
        }
        let mut new_indices = Sorted::<usize, 16>::default();
        new_indices.consume_indirect(&mut indices);
        for (i, (key, child)) in new_indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_indirect_from_sorted() {
        let mut indices = Sorted::<usize, 16>::default();
        for i in 0..16 {
            indices.add_child(i, i as usize);
        }
        let mut new_indices = Indirect::<usize, 48>::default();
        new_indices.consume_sorted(&mut indices);
        for (i, (key, child)) in new_indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_indirect_from_direct() {
        let mut indices = Direct::<usize>::default();
        for i in 0..48 {
            indices.add_child(i, i as usize);
        }
        let mut new_indices = Indirect::<usize, 48>::default();
        new_indices.consume_direct(&mut indices);
        for (i, (key, child)) in new_indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }

    #[test]
    fn test_direct_from_indirect() {
        let mut indices = Indirect::<usize, 48>::default();
        for i in 0..48 {
            indices.add_child(i, i as usize);
        }
        let mut new_indices = Direct::<usize>::default();
        new_indices.consume_indirect(&mut indices);
        for (i, (key, child)) in new_indices.into_iter().enumerate() {
            assert_eq!(i, key as usize);
            assert_eq!(i, *child);
        }
    }
}
