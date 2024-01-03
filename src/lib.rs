//! A library containing an implementation of Adaptive Radix Tree.

#![warn(
    clippy::pedantic,
    clippy::cargo,
    clippy::nursery,
    rustdoc::all,
    missing_debug_implementations
)]
#![deny(clippy::all, missing_docs, rust_2018_idioms, rust_2021_compatibility)]

mod art;

pub use art::*;
