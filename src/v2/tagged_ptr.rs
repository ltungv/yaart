//! A tagged pointer is a pointer (concretely a memory address) with additional data associated
//! with it, such as an indirection bit or reference count. This additional data is often "folded"
//! into the pointer, meaning stored inline in the data representing the address, taking advantage
//! of certain properties of memory addressing.
//!
//! Most architectures are byte-addressable (the smallest addressable unit is a byte), but certain
//! types of data will often be aligned to the size of the data, often a word or multiple thereof.
//! This discrepancy leaves a few of the least significant bits of the pointer unused, which can be
//! used for tags – most often as a bit field (each bit a separate tag) – as long as code that uses
//! the pointer masks out these bits before accessing memory

use std::{fmt, mem::align_of, num::NonZeroUsize, ptr::NonNull};

/// A non-nullable pointer carrying free bits of metadata.
///
/// The `TAG_BITS` const generic determines the number of free least significant bits that must be
/// available in the representation of the memory address. It is ensured that the pointed-to type's
/// alignment is sufficient to carry at least `TAG_BITS` free bits. The correctness of the memory
/// representation is checked at compile time and any error will be reported by the compiler.
#[repr(transparent)]
pub struct TaggedPtr<P, const TAG_BITS: u32>(NonNull<P>);

impl<P, const TAG_BITS: u32> Copy for TaggedPtr<P, TAG_BITS> {}
impl<P, const TAG_BITS: u32> Clone for TaggedPtr<P, TAG_BITS> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<P, const TAG_BITS: u32> From<&mut P> for TaggedPtr<P, TAG_BITS> {
    fn from(reference: &mut P) -> Self {
        unsafe { Self::new_unchecked(reference) }
    }
}

impl<P, const TAG_BITS: u32> From<NonNull<P>> for TaggedPtr<P, TAG_BITS> {
    fn from(pointer: NonNull<P>) -> Self {
        unsafe { Self::new_unchecked(pointer.as_ptr()) }
    }
}

impl<P, const TAG_BITS: u32> From<TaggedPtr<P, TAG_BITS>> for NonNull<P> {
    fn from(tagged_ptr: TaggedPtr<P, TAG_BITS>) -> NonNull<P> {
        tagged_ptr.as_ptr()
    }
}

impl<P, const TAG_BITS: u32> std::hash::Hash for TaggedPtr<P, TAG_BITS> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

impl<P, const TAG_BITS: u32> Eq for TaggedPtr<P, TAG_BITS> {}
impl<P, const TAG_BITS: u32> PartialEq for TaggedPtr<P, TAG_BITS> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<P, const TAG_BITS: u32> fmt::Debug for TaggedPtr<P, TAG_BITS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TaggedPtr")
            .field("ptr", &self.as_ptr())
            .field("tags", &self.as_tags())
            .finish()
    }
}

impl<P, const TAG_BITS: u32> fmt::Pointer for TaggedPtr<P, TAG_BITS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}

impl<P, const TAG_BITS: u32> TaggedPtr<P, TAG_BITS> {
    /// The alignment of the pointed-to data.
    pub const ALIGNMENT: usize = align_of::<P>();

    /// The number of free bits in the representation of memory addresses.
    pub const FREE_BITS: u32 = {
        let free_bits = Self::ALIGNMENT.trailing_zeros();
        assert!(free_bits >= TAG_BITS, "insufficient free bits",);
        free_bits
    };

    /// The bit mask for getting a normalized pointer.
    pub const MASK_PTR: usize = usize::MAX << Self::FREE_BITS;

    /// The bit mask for getting the pointer's tags.
    pub const MARK_TAGS: usize = !Self::MASK_PTR;

    /// Returns a tagged pointer based on the given raw pointer if it is not null.
    pub fn new(pointer: *mut P) -> Option<Self> {
        if pointer.is_null() {
            return None;
        }
        unsafe { Some(Self::new_unchecked(pointer)) }
    }

    /// Returns a tagged pointer based on the given raw pointer without checking if it is null.
    pub unsafe fn new_unchecked(pointer: *mut P) -> Self {
        let unchecked_ptr = unsafe { NonNull::new_unchecked(pointer) };
        assert_eq!(
            unchecked_ptr.addr().get() & Self::MARK_TAGS,
            0,
            "unaligned pointer"
        );
        Self(unchecked_ptr)
    }

    /// Gets the normalized pointer from the tagged pointer.
    #[inline]
    pub fn as_ptr(self) -> NonNull<P> {
        self.0
            .map_addr(|addr| unsafe { NonZeroUsize::new_unchecked(addr.get() & Self::MASK_PTR) })
    }

    /// Get the tags from the tagged pointer.
    #[inline]
    pub fn as_tags(self) -> usize {
        self.0.addr().get() & Self::MARK_TAGS
    }

    /// Updates the value of the tags in the pointer.
    pub fn tags(&mut self, tags: usize) {
        assert_eq!(tags & Self::MASK_PTR, 0, "overflowing tags");
        let tags = tags & Self::MARK_TAGS;
        self.0 = self.0.map_addr(|addr| unsafe {
            NonZeroUsize::new_unchecked(addr.get() & Self::MASK_PTR) | tags
        });
    }
}

#[allow(clippy::similar_names)]
#[cfg(test)]
mod tests {
    use super::*;

    fn tags_beyond_capacity<T, const TAG_BITS: u32>()
    where
        T: Default,
    {
        let mut pointee = T::default();
        let mut tagged_ptr = TaggedPtr::<_, TAG_BITS>::new(&raw mut pointee).unwrap();
        let free_bits = std::mem::align_of::<T>().trailing_zeros();
        tagged_ptr.tags(usize::MAX >> (usize::BITS - free_bits - 1));
    }

    #[test]
    fn it_works() {
        let mut pointee = "Hello world!";
        let mut tagged_ptr = TaggedPtr::<&str, 3>::new(&raw mut pointee).unwrap();

        // First tags.
        tagged_ptr.tags(0b101);
        assert_eq!(tagged_ptr.as_tags(), 0b101);
        assert_eq!(unsafe { *tagged_ptr.as_ptr().as_ptr() }, "Hello world!");

        // Second tags.
        tagged_ptr.tags(0b010);
        assert_eq!(tagged_ptr.as_tags(), 0b010);
        assert_eq!(unsafe { *tagged_ptr.as_ptr().as_ptr() }, "Hello world!");
    }

    #[should_panic = "overflowing tags"]
    #[test]
    fn tags_beyond_capacity_u8() {
        tags_beyond_capacity::<u8, 0>();
    }

    #[should_panic = "overflowing tags"]
    #[test]
    fn tags_beyond_capacity_u16() {
        tags_beyond_capacity::<u16, 1>();
    }

    #[should_panic = "overflowing tags"]
    #[test]
    fn tags_beyond_capacity_u32() {
        tags_beyond_capacity::<u32, 2>();
    }

    #[should_panic = "overflowing tags"]
    #[test]
    fn tags_beyond_capacity_u64() {
        tags_beyond_capacity::<u64, 3>();
    }

    #[should_panic = "overflowing tags"]
    #[test]
    fn tags_beyond_capacity_u128() {
        tags_beyond_capacity::<u128, 4>();
    }

    #[test]
    fn tags_of_various_sizes() {
        fn assert<T, const TAG_BITS: u32>()
        where
            T: fmt::Debug + Default + PartialEq,
        {
            let mut pointee = T::default();
            let mut tagged_ptr = TaggedPtr::<_, TAG_BITS>::new(&raw mut pointee).unwrap();
            let free_bits = std::mem::align_of::<T>().trailing_zeros();
            let tags = if free_bits == 0 {
                0
            } else {
                usize::MAX >> (usize::BITS - free_bits)
            };
            tagged_ptr.tags(tags);
            assert_eq!(tagged_ptr.as_tags(), tags,);
            assert_eq!(unsafe { &*tagged_ptr.as_ptr().as_ptr() }, &pointee);
        }
        assert::<u8, 0>();
        assert::<u16, 1>();
        assert::<u32, 2>();
        assert::<u64, 3>();
        assert::<u128, 4>();
    }

    #[allow(edition_2024_expr_fragment_specifier)]
    #[cfg(target_pointer_width = "64")]
    #[test]
    fn alignment_bits_and_mask_values() {
        fn assert<T, const TAG_BITS: u32>() {
            assert_eq!(
                TaggedPtr::<T, TAG_BITS>::ALIGNMENT,
                std::mem::align_of::<T>()
            );
            assert_eq!(
                TaggedPtr::<T, TAG_BITS>::FREE_BITS,
                std::mem::align_of::<T>().trailing_zeros()
            );
            assert_eq!(
                TaggedPtr::<T, TAG_BITS>::MASK_PTR,
                usize::MAX << std::mem::align_of::<T>().trailing_zeros()
            );
        }
        assert::<(), 0>();
        assert::<u8, 0>();
        assert::<u16, 0>();
        assert::<u32, 0>();
        assert::<u64, 0>();
        assert::<u128, 0>();
    }
}
