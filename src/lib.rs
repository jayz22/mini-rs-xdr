#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "next")]
pub mod next;
#[cfg(feature = "next")]
pub use next::*;
