use std::{
    mem::MaybeUninit,
    ops::{Index, IndexMut},
};

/// A vector with fixed capacity.
#[derive(Debug)]
pub struct StaticVec<T, const N: usize> {
    len: usize,
    data: [MaybeUninit<T>; N],
}

impl<T, const N: usize> Default for StaticVec<T, N> {
    fn default() -> Self {
        Self {
            len: 0,
            // SAFETY: calling `assume_init` to convert an uninitialized array
            // into an array of uninitialized items is safe.
            data: unsafe { MaybeUninit::uninit().assume_init() },
        }
    }
}

impl<T, const N: usize> Index<usize> for StaticVec<T, N> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        if index >= self.len {
            panic!("index {} out of bounds", index);
        }
        // SAFETY: Any index less than `self.len` must have been initialized.
        unsafe { self.data[index].assume_init_ref() }
    }
}

impl<T, const N: usize> IndexMut<usize> for StaticVec<T, N> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index >= self.len {
            panic!("index {} out of bounds", index);
        }
        // SAFETY: Any index less than `self.len` must have been initialized.
        unsafe { self.data[index].assume_init_mut() }
    }
}

impl<T, const N: usize> AsRef<[T]> for StaticVec<T, N> {
    fn as_ref(&self) -> &[T] {
        // SAFETY: casting `self.data[..self.len]` to a `*const [MaybeUninit<T>]`
        // is safe since we guarantee that `self.data[..self.len]` is initialized,
        // and `MaybeUninit` is guaranteed to have the same layout as `T`. The
        // pointer obtained is valid since it refers to memory owned by `self.data`
        // which is a reference and thus guaranteed to be valid for reads.
        unsafe {
            let as_uninit = &self.data[..self.len] as *const [MaybeUninit<T>];
            let as_init = as_uninit as *const [T];
            &*as_init
        }
    }
}

impl<T, const N: usize> AsMut<[T]> for StaticVec<T, N> {
    fn as_mut(&mut self) -> &mut [T] {
        // SAFETY: casting `self.data[..self.len]` to a `*mut [MaybeUninit<T>]`
        // is safe since we guarantee that `self.data[..self.len]` is initialized,
        // and `MaybeUninit` is guaranteed to have the same layout as `T`. The
        // pointer obtained is valid since it refers to memory owned by `self.data`
        // which is a reference and thus guaranteed to be valid for reads and writes.
        unsafe {
            let as_uninit = &mut self.data[..self.len] as *mut [MaybeUninit<T>];
            let as_init = as_uninit as *mut [T];
            &mut *as_init
        }
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a StaticVec<T, N> {
    type Item = &'a T;

    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_ref().iter()
    }
}

impl<'a, T, const N: usize> IntoIterator for &'a mut StaticVec<T, N> {
    type Item = &'a mut T;

    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.as_mut().iter_mut()
    }
}

impl<T, const N: usize> StaticVec<T, N> {
    /// Push a value into the vector, returning an error if the vector is full.
    pub fn push_within_capacity(&mut self, value: T) -> Result<(), T> {
        if self.len >= N {
            return Err(value);
        }
        self.data[self.len] = MaybeUninit::new(value);
        self.len += 1;
        Ok(())
    }

    /// Get the length of the vector.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Get an iterator over the vector.
    pub fn iter(&self) -> std::slice::Iter<T> {
        self.into_iter()
    }

    /// Get a mutable iterator over the vector.
    pub fn iter_mut(&mut self) -> std::slice::IterMut<T> {
        self.into_iter()
    }

    pub fn search_linear(&self, key: &T) -> Option<usize>
    where
        T: PartialEq,
    {
        self.iter()
            .enumerate()
            .find(|(_, k)| key.eq(*k))
            .map(|(i, _)| i)
    }
}

#[cfg(test)]
mod tests {
    use super::StaticVec;

    #[test]
    fn test_basic_usages() {
        // Initialization.
        let mut v = StaticVec::<usize, 16>::default();
        assert_eq!(v.len(), 0);

        // Insert until limit.
        for i in 0..16 {
            assert_eq!(v.push_within_capacity(i), Ok(()));
        }

        // Error on over-full.
        assert_eq!(v.push_within_capacity(16), Err(16));
        assert_eq!(v.len(), 16);

        // Iterate and search for item.
        for (i, x) in v.iter().enumerate() {
            assert_eq!(*x, i);
            assert_eq!(v[i], i);
            assert_eq!(v.search_linear(x), Some(i));
        }
    }

    #[test]
    fn test_mutations() {
        let mut v = StaticVec::<usize, 16>::default();
        for i in 0..16 {
            v.push_within_capacity(i).unwrap();
        }
        for x in v.iter_mut() {
            *x += 1;
        }
        for i in 0..16 {
            v[i] *= 2;
        }
        for (i, x) in v.iter().enumerate() {
            assert_eq!(*x, (i + 1) * 2);
        }
    }
}
