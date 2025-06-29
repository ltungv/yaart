use super::{AsSearchKey, KeyMapping};

#[derive(Debug)]
pub struct Identity;

impl<T> KeyMapping<T> for Identity
where
    T: AsSearchKey,
{
    type Key = T;

    fn to_bytes(value: T) -> Self::Key {
        value
    }

    fn from_bytes(bytes: Self::Key) -> T {
        bytes
    }
}
