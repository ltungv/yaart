use super::{BytesMapping, BytesRepr};

#[derive(Debug)]
pub struct Identity;

impl<T> BytesMapping<T> for Identity
where
    T: BytesRepr,
{
    type Key = T;

    fn to_bytes(value: T) -> Self::Key {
        value
    }

    fn from_bytes(bytes: Self::Key) -> T {
        bytes
    }
}
