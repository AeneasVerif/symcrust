#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

#[derive(Default, PartialEq, Clone, Copy)]
#[repr(align(16))]
#[repr(C)]
pub
struct SYMCRYPT_KECCAK_STATE
{
  pub state: [u64; 25],
  pub inputBlockSize: u32,
  pub stateIndex: u32,
  pub paddingValue: u8,
  pub squeezeMode: u8
}

#[derive(Default, PartialEq, Clone, Copy)]
#[repr(align(16))]
#[repr(C)]
pub
struct SYMCRYPT_SHA3_224_STATE
{ pub ks: SYMCRYPT_KECCAK_STATE, pub magic: usize }

#[derive(Default, PartialEq, Clone, Copy)]
#[repr(align(16))]
#[repr(C)]
pub
struct SYMCRYPT_SHA3_256_STATE
{ pub ks: SYMCRYPT_KECCAK_STATE, pub magic: usize }

#[derive(Default, PartialEq, Clone, Copy)]
#[repr(align(16))]
#[repr(C)]
pub
struct SYMCRYPT_SHA3_384_STATE
{ pub ks: SYMCRYPT_KECCAK_STATE, pub magic: usize }

#[derive(Default, PartialEq, Clone, Copy)]
#[repr(align(16))]
#[repr(C)]
pub
struct SYMCRYPT_SHA3_512_STATE
{ pub ks: SYMCRYPT_KECCAK_STATE, pub magic: usize }

#[derive(Default, PartialEq, Clone, Copy)]
#[repr(align(16))]
#[repr(C)]
pub
struct SYMCRYPT_SHAKE128_STATE
{ pub ks: SYMCRYPT_KECCAK_STATE, pub magic: usize }

#[derive(Default, PartialEq, Clone, Copy)]
#[repr(align(16))]
#[repr(C)]
pub
struct SYMCRYPT_SHAKE256_STATE
{ pub ks: SYMCRYPT_KECCAK_STATE, pub magic: usize }
