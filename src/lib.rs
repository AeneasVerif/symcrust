// Allow using the `charon` attributes
#![feature(register_tool)]
#![register_tool(charon)]

// For the `alloc` module
#![feature(allocator_api)]
#![feature(try_with_capacity)]

#![allow(dead_code)]
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]

#![feature(try_trait_v2)]

pub mod common;
pub mod hash;
pub mod key;
pub mod ntt;
pub mod mlkem;
pub mod ffi;

#[cfg(test)]
pub mod test;
