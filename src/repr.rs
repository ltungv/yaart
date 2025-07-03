mod identity;
mod mapped;
mod to_big_endian;

pub use identity::*;
pub use mapped::*;
pub use to_big_endian::*;

use super::search_key::SearchKey;

/// Any type implementing this trait can be decomposed into bytes.
pub trait BytesRepr {
    /// Views the bytes representation of this value through a [`SearchKey`].
    fn repr(&self) -> SearchKey<'_>;
}

/// Any type implementing this trait can be decomposed into bytes and the order between decomposed
/// bytes remain the same as the order between original values.
pub trait OrderedBytesRepr: BytesRepr + Ord {}

/// Any type implementing this trait can be converted from/into some type implementing
/// [`BytesRepr`].
pub trait BytesMapping<T> {
    /// The type of the byte container that a value will be converted into.
    type Key: BytesRepr;

    /// Converts a value into its bytes representation.
    fn to_bytes(value: T) -> Self::Key;

    /// Converts a bytes representation into its value.
    fn from_bytes(bytes: Self::Key) -> T;
}

macro_rules! impl_bytes_repr_for_integer {
    ($T:ty) => {
        impl BytesRepr for $T {
            fn repr(&self) -> SearchKey<'_> {
                bytemuck::bytes_of(self).into()
            }
        }

        impl BytesRepr for [$T] {
            fn repr(&self) -> SearchKey<'_> {
                bytemuck::cast_slice(self).into()
            }
        }

        impl BytesRepr for Vec<$T> {
            fn repr(&self) -> SearchKey<'_> {
                bytemuck::cast_slice(self).into()
            }
        }

        impl<const N: usize> BytesRepr for [$T; N] {
            fn repr(&self) -> SearchKey<'_> {
                bytemuck::cast_slice(self).into()
            }
        }
    };
}

impl_bytes_repr_for_integer!(i8);
impl_bytes_repr_for_integer!(i16);
impl_bytes_repr_for_integer!(i32);
impl_bytes_repr_for_integer!(i64);
impl_bytes_repr_for_integer!(i128);

impl_bytes_repr_for_integer!(u8);
impl_bytes_repr_for_integer!(u16);
impl_bytes_repr_for_integer!(u32);
impl_bytes_repr_for_integer!(u64);
impl_bytes_repr_for_integer!(u128);

impl BytesRepr for str {
    fn repr(&self) -> SearchKey<'_> {
        self.as_bytes().into()
    }
}

impl BytesRepr for String {
    fn repr(&self) -> SearchKey<'_> {
        self.as_bytes().into()
    }
}

impl<T> BytesRepr for &T
where
    T: BytesRepr + ?Sized,
{
    fn repr(&self) -> SearchKey<'_> {
        T::repr(*self)
    }
}

impl OrderedBytesRepr for [u8] {}

impl OrderedBytesRepr for Vec<u8> {}

impl<const N: usize> OrderedBytesRepr for [u8; N] {}

impl OrderedBytesRepr for str {}

impl OrderedBytesRepr for String {}

impl<T> OrderedBytesRepr for &T where T: OrderedBytesRepr + ?Sized {}

#[cfg(test)]
mod tests {
    use super::BytesRepr;

    #[test]
    fn various_numeric_types_as_bytes() {
        assert_eq!(u8::MAX.repr().as_ref(), &[u8::MAX]);
        assert_eq!(i8::MAX.repr().as_ref(), &[i8::MAX as u8]);
        assert_eq!(65535u16.repr().as_ref(), 65535u16.to_ne_bytes());
        assert_eq!(32767i16.repr().as_ref(), 32767i16.to_ne_bytes());
        assert_eq!(2387u32.repr().as_ref(), 2387u32.to_ne_bytes());
        assert_eq!(2387i32.repr().as_ref(), 2387i32.to_ne_bytes());

        // numeric arrays
        assert_eq!(
            [26343u16, 0, u16::MAX].repr().as_ref(),
            &[26343u16.to_ne_bytes()[0], 26343u16.to_ne_bytes()[1], 0, 0, 255, 255]
        );
        assert_eq!(
            Box::<[u16]>::from([26343u16, 0, u16::MAX]).repr().as_ref(),
            &[26343u16.to_ne_bytes()[0], 26343u16.to_ne_bytes()[1], 0, 0, 255, 255]
        );
        assert_eq!(
            Vec::<u16>::from([26343u16, 0, u16::MAX]).repr().as_ref(),
            &[26343u16.to_ne_bytes()[0], 26343u16.to_ne_bytes()[1], 0, 0, 255, 255]
        );
    }
}
