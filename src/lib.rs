// Allow using the `charon` attributes
#![feature(register_tool)]
#![register_tool(charon)]

// For the `alloc` module
#![feature(allocator_api)]
#![feature(try_with_capacity)]

pub mod common;
pub mod hash;
pub mod key;
pub mod ntt;
pub mod mlkem;
pub mod misc;
pub mod test;
