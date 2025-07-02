use crate::compressed_path::CompressedPath;

#[derive(Debug, Clone)]
#[repr(C)]
pub struct Header<const PARTIAL_LEN: usize> {
    pub children: u16,
    pub path: CompressedPath<PARTIAL_LEN>,
}

impl<const PARTIAL_LEN: usize> From<CompressedPath<PARTIAL_LEN>> for Header<PARTIAL_LEN> {
    fn from(path: CompressedPath<PARTIAL_LEN>) -> Self {
        Self { children: 0, path }
    }
}
