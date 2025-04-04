// Allows using the `charon` attributes
#![feature(register_tool)]
#![register_tool(charon)]
// To hook up box::try_new_in to the client-provided SymCrypt allocation callback.
#![feature(allocator_api)]
// To catch allocation failures when creating TEMPORARIES.
#![feature(try_with_capacity)]
// Make crate::common::ERROR compose with the ? operator and the std::result::Result type.
#![feature(try_trait_v2)]

pub mod common;
pub mod ffi;
pub mod hash;
pub mod key;
pub mod mlkem;
pub mod ntt;

#[cfg(test)]
pub mod test;
