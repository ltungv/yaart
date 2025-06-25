use std::{rc::Rc, sync::Arc};

use crate::SearchKey;

/// A type that can be turn into bytes for comparison.
pub trait BytesComparable {
    /// The container type that holds the bytes representing our value, which can be
    /// referenced to get the slice of bytes.
    type Target<'a>: 'a + AsRef<[u8]>
    where
        Self: 'a;

    /// Turn the value into a [`SearchKey`] of some container of bytes.
    fn key(&self) -> SearchKey<Self::Target<'_>>;
}

impl BytesComparable for u8 {
    type Target<'a> = [Self; 1];

    fn key(&self) -> SearchKey<Self::Target<'static>> {
        SearchKey::new(self.to_be_bytes())
    }
}

impl BytesComparable for u16 {
    type Target<'a> = [u8; 2];

    fn key(&self) -> SearchKey<Self::Target<'static>> {
        SearchKey::new(self.to_be_bytes())
    }
}

impl BytesComparable for u32 {
    type Target<'a> = [u8; 4];

    fn key(&self) -> SearchKey<Self::Target<'static>> {
        SearchKey::new(self.to_be_bytes())
    }
}

impl BytesComparable for u64 {
    type Target<'a> = [u8; 8];

    fn key(&self) -> SearchKey<Self::Target<'static>> {
        SearchKey::new(self.to_be_bytes())
    }
}

impl BytesComparable for u128 {
    type Target<'a> = [u8; 16];

    fn key(&self) -> SearchKey<Self::Target<'static>> {
        SearchKey::new(self.to_be_bytes())
    }
}

impl BytesComparable for i8 {
    type Target<'a> = [u8; 1];

    fn key(&self) -> SearchKey<Self::Target<'static>> {
        SearchKey::new((self ^ (1 << (Self::BITS - 1))).to_be_bytes())
    }
}

impl BytesComparable for i16 {
    type Target<'a> = [u8; 2];

    fn key(&self) -> SearchKey<Self::Target<'static>> {
        SearchKey::new((self ^ (1 << (Self::BITS - 1))).to_be_bytes())
    }
}

impl BytesComparable for i32 {
    type Target<'a> = [u8; 4];

    fn key(&self) -> SearchKey<Self::Target<'static>> {
        SearchKey::new((self ^ (1 << (Self::BITS - 1))).to_be_bytes())
    }
}

impl BytesComparable for i64 {
    type Target<'a> = [u8; 8];

    fn key(&self) -> SearchKey<Self::Target<'static>> {
        SearchKey::new((self ^ (1 << (Self::BITS - 1))).to_be_bytes())
    }
}

impl BytesComparable for i128 {
    type Target<'a> = [u8; 16];

    fn key(&self) -> SearchKey<Self::Target<'static>> {
        SearchKey::new((self ^ (1 << (Self::BITS - 1))).to_be_bytes())
    }
}

impl BytesComparable for String {
    type Target<'a> = &'a [u8];

    fn key(&self) -> SearchKey<Self::Target<'_>> {
        SearchKey::new(self.as_bytes())
    }
}

impl BytesComparable for Rc<str> {
    type Target<'a> = &'a [u8];

    fn key(&self) -> SearchKey<Self::Target<'_>> {
        SearchKey::new(self.as_bytes())
    }
}

impl BytesComparable for Arc<str> {
    type Target<'a> = &'a [u8];

    fn key(&self) -> SearchKey<Self::Target<'_>> {
        SearchKey::new(self.as_bytes())
    }
}

impl BytesComparable for str {
    type Target<'a> = &'a [u8];

    fn key(&self) -> SearchKey<Self::Target<'_>> {
        SearchKey::new(self.as_bytes())
    }
}

impl BytesComparable for &str {
    type Target<'a>
        = &'a [u8]
    where
        Self: 'a;

    fn key(&self) -> SearchKey<Self::Target<'_>> {
        SearchKey::new(self.as_bytes())
    }
}

impl BytesComparable for Vec<u8> {
    type Target<'a> = &'a [u8];

    fn key(&self) -> SearchKey<Self::Target<'_>> {
        SearchKey::new(self.as_slice())
    }
}

impl BytesComparable for [u8] {
    type Target<'a> = &'a [u8];

    fn key(&self) -> SearchKey<Self::Target<'_>> {
        SearchKey::new(self)
    }
}

impl BytesComparable for &[u8] {
    type Target<'a>
        = &'a [u8]
    where
        Self: 'a;

    fn key(&self) -> SearchKey<Self::Target<'_>> {
        SearchKey::new(self)
    }
}
