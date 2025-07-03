use super::{BytesMapping, Mapped, OrderedBytesRepr};

/// A [`BytesMapping`] that maps between integral values and their bytes representation in
/// big-endian order.
#[derive(Debug)]
pub struct ToBigEndian;

macro_rules! impl_to_big_endian_for_integer {
    ($signed:ty, $unsigned:ty) => {
        impl BytesMapping<$signed> for ToBigEndian {
            type Key = [u8; std::mem::size_of::<$signed>()];

            fn to_bytes(value: $signed) -> Self::Key {
                let unsigned = bytemuck::cast::<_, $unsigned>(value);
                (unsigned ^ (1 << (<$signed>::BITS - 1))).to_be_bytes()
            }

            fn from_bytes(bytes: Self::Key) -> $signed {
                let unsigned = <$unsigned>::from_be_bytes(bytes);
                bytemuck::cast::<_, $signed>(unsigned ^ (1 << (<$signed>::BITS - 1)))
            }
        }

        impl BytesMapping<$unsigned> for ToBigEndian {
            type Key = [u8; std::mem::size_of::<$unsigned>()];

            fn to_bytes(value: $unsigned) -> Self::Key {
                value.to_be_bytes()
            }

            fn from_bytes(bytes: Self::Key) -> $unsigned {
                <$unsigned>::from_be_bytes(bytes)
            }
        }

        impl PartialOrd for Mapped<ToBigEndian, $signed> {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl PartialOrd for Mapped<ToBigEndian, $unsigned> {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(other))
            }
        }

        impl Ord for Mapped<ToBigEndian, $signed> {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.as_ref().cmp(other.as_ref())
            }
        }

        impl Ord for Mapped<ToBigEndian, $unsigned> {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.as_ref().cmp(other.as_ref())
            }
        }

        impl OrderedBytesRepr for Mapped<ToBigEndian, $signed> {}
        impl OrderedBytesRepr for Mapped<ToBigEndian, $unsigned> {}
    };
}

impl_to_big_endian_for_integer!(i8, u8);
impl_to_big_endian_for_integer!(i16, u16);
impl_to_big_endian_for_integer!(i32, u32);
impl_to_big_endian_for_integer!(i64, u64);
impl_to_big_endian_for_integer!(i128, u128);
