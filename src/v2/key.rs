mod identity;
mod mapped;
mod to_big_endian;

use super::search_key::SearchKey;

pub use identity::*;
pub use mapped::*;
pub use to_big_endian::*;

pub trait AsSearchKey {
    fn key(&self) -> SearchKey<'_>;
}

pub trait OrderedSearchKey: AsSearchKey + Ord {}

pub trait KeyMapping<T> {
    type Key: AsSearchKey;

    fn to_bytes(value: T) -> Self::Key;

    fn from_bytes(bytes: Self::Key) -> T;
}

macro_rules! impl_as_search_key_for_integer {
    ($T:ty) => {
        impl AsSearchKey for $T {
            fn key(&self) -> SearchKey<'_> {
                SearchKey::new(bytemuck::bytes_of(self))
            }
        }

        impl AsSearchKey for [$T] {
            fn key(&self) -> SearchKey<'_> {
                SearchKey::new(bytemuck::cast_slice(self))
            }
        }

        impl AsSearchKey for Vec<$T> {
            fn key(&self) -> SearchKey<'_> {
                SearchKey::new(bytemuck::cast_slice(self))
            }
        }

        impl<const N: usize> AsSearchKey for [$T; N] {
            fn key(&self) -> SearchKey<'_> {
                SearchKey::new(bytemuck::cast_slice(self))
            }
        }
    };
}

impl_as_search_key_for_integer!(i8);
impl_as_search_key_for_integer!(i16);
impl_as_search_key_for_integer!(i32);
impl_as_search_key_for_integer!(i64);
impl_as_search_key_for_integer!(i128);

impl_as_search_key_for_integer!(u8);
impl_as_search_key_for_integer!(u16);
impl_as_search_key_for_integer!(u32);
impl_as_search_key_for_integer!(u64);
impl_as_search_key_for_integer!(u128);

#[cfg(test)]
mod tests {
    use super::AsSearchKey;

    #[test]
    fn various_numeric_types_as_bytes() {
        assert_eq!(u8::MAX.key().as_ref(), &[u8::MAX]);
        assert_eq!(i8::MAX.key().as_ref(), &[i8::MAX as u8]);
        assert_eq!(65535u16.key().as_ref(), 65535u16.to_ne_bytes());
        assert_eq!(32767i16.key().as_ref(), 32767i16.to_ne_bytes());
        assert_eq!(2387u32.key().as_ref(), 2387u32.to_ne_bytes());
        assert_eq!(2387i32.key().as_ref(), 2387i32.to_ne_bytes());

        // numeric arrays
        assert_eq!(
            [26343u16, 0, u16::MAX].key().as_ref(),
            &[
                26343u16.to_ne_bytes()[0],
                26343u16.to_ne_bytes()[1],
                0,
                0,
                255,
                255
            ]
        );
        assert_eq!(
            Box::<[u16]>::from([26343u16, 0, u16::MAX]).key().as_ref(),
            &[
                26343u16.to_ne_bytes()[0],
                26343u16.to_ne_bytes()[1],
                0,
                0,
                255,
                255
            ]
        );
        assert_eq!(
            Vec::<u16>::from([26343u16, 0, u16::MAX]).key().as_ref(),
            &[
                26343u16.to_ne_bytes()[0],
                26343u16.to_ne_bytes()[1],
                0,
                0,
                255,
                255
            ]
        );
    }
}
