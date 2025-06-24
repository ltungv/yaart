//! # Adaptive Radix Tree

#![deny(
    clippy::all,
    rust_2018_idioms,
    rust_2024_compatibility,
    rust_2021_compatibility,
    missing_debug_implementations,
    missing_docs
)]
#![warn(rustdoc::all, clippy::pedantic, clippy::nursery)]

mod art;
mod bytes_comparable;
mod compressed_path;
mod index;
mod node;

pub use art::*;
pub use bytes_comparable::*;
