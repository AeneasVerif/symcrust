// This module contains reverse-bindings that expose our Rust implementations with a C ABI,
// identical to that exposed in symcrypt.h
//
// The primary goal of this module is to expose just enough functions that the unit test can run
// performance benchmarks on our Rust implementation.
//
// SymCrypt enforces abstraction by using an incomplete struct type for the PMLKEMKEY object,
// and the test driver uses only the public API, meaning we can lie and use another (Rust) type for
// the key as long as it's behind a pointer.

use libc::{c_int,size_t};
use crate::common::MLKEM_ERROR;

// TYPE DEFINITIONS
// ----------------

// C11 enums are `int`, per the C standard
type c_params = c_int;
type c_format = c_int;

// This type has repr(C) -- it can be shuttled back and forth.
type c_error = crate::common::MLKEM_ERROR;

// So the dynamically-sized type (DST) comes back to bite us. The KEY type is a DST, meaning that
// in Rust it's a fat pointer -- it does not implement the Thin trait, and as such cannot be passed
// via the FFI. We add another layer of indirection.
type c_key = *mut Box<crate::key::KEY>;

// CONVERSIONS
// -----------

impl TryFrom<c_int> for crate::key::PARAMS {
    type Error = MLKEM_ERROR;
    fn try_from(params: c_int) -> Result<crate::key::PARAMS, MLKEM_ERROR> {
        match params {
            0 => Result::Err(MLKEM_ERROR::INCOMPATIBLE_FORMAT),
            1 => Result::Ok(crate::key::PARAMS::MLKEM512),
            2 => Result::Ok(crate::key::PARAMS::MLKEM768),
            3 => Result::Ok(crate::key::PARAMS::MLKEM1024),
            _ => Result::Err(MLKEM_ERROR::INVALID_ARGUMENT)
        }
    }
}

impl TryFrom<c_int> for crate::key::FORMAT {
    type Error = MLKEM_ERROR;
    fn try_from(format: c_int) -> Result<crate::key::FORMAT, MLKEM_ERROR> {
        match format {
            0 => Result::Err(MLKEM_ERROR::INCOMPATIBLE_FORMAT),
            1 => Result::Ok(crate::key::FORMAT::PRIVATE_SEED),
            2 => Result::Ok(crate::key::FORMAT::DECAPSULATION_KEY),
            3 => Result::Ok(crate::key::FORMAT::ENCAPSULATION_KEY),
            _ => Result::Err(MLKEM_ERROR::INVALID_ARGUMENT)
        }
    }
}

// Allows using the ? operator to early-return in functions that return MLKEM_ERROR.
impl std::ops::FromResidual<Result<std::convert::Infallible, MLKEM_ERROR>> for MLKEM_ERROR {
    fn from_residual(r: Result<std::convert::Infallible, MLKEM_ERROR>) -> MLKEM_ERROR {
        match r {
            Result::Ok(_) => MLKEM_ERROR::NO_ERROR,
            Result::Err(e) => e
        }
    }
}

// API
// ---

#[no_mangle] pub extern "C"
fn SymCryptMlKemkeyAllocate(params: c_int) -> c_key {
    match crate::key::PARAMS::try_from(params) {
        Result::Err(_) => std::ptr::null_mut(),
        Result::Ok(params) => {
            match crate::key::KeyAllocate(params) {
                Result::Err(_) => std::ptr::null_mut(),
                Result::Ok(k) => Box::into_raw(Box::new(k))
            }
        }
    }
}

#[no_mangle] pub extern "C"
fn SymCryptMlKemKeyFree(k: c_key) {
    let _ = unsafe { Box::from_raw(k) };
    // Drop trait gets called here, presumably.
}

#[no_mangle] pub extern "C"
fn SymCryptMlKemSizeofKeyFormatFromParams(params: c_params, format: c_format, sz: &mut size_t) -> MLKEM_ERROR {
    *sz = crate::mlkem::SymCryptMlKemSizeofKeyFormatFromParams(params.try_into()?, format.try_into()?);
    MLKEM_ERROR::NO_ERROR
}

#[no_mangle] pub extern "C"
fn SymCryptMlKemSizeofCiphertextFromParams(params: c_params, sz: &mut size_t) -> MLKEM_ERROR {
    *sz = crate::mlkem::SymCryptMlKemSizeofCiphertextFromParams(params.try_into()?);
    MLKEM_ERROR::NO_ERROR
}

#[no_mangle] pub extern "C"
fn SymCryptMlKemkeyGenerate(k: c_key, flags: u32) -> MLKEM_ERROR {
    let mut k = unsafe { Box::from_raw(k) };
    // Note: the * can be inserted by Rust automatically
    let r = crate::mlkem::SymCryptMlKemkeyGenerate(&mut (*k), flags);
    // Note: we probably (check) need this to prevent Drop from being called.
    let _ = Box::into_raw(k);
    r
}

#[no_mangle] pub extern "C"
fn SymCryptMlKemkeySetValue(pbSrc: *const u8, cbSrc: size_t, format: c_format, flags: u32, k: c_key) -> MLKEM_ERROR {
    let mut k = unsafe { Box::from_raw(k) };
    let src = unsafe { std::slice::from_raw_parts(pbSrc, cbSrc) };
    let r = crate::mlkem::SymCryptMlKemkeySetValue(src, format.try_into()?, flags, &mut (*k));
    // Note: we probably (check) need this to prevent Drop from being called.
    let _ = Box::into_raw(k);
    r
}

#[no_mangle] pub extern "C"
fn SymCryptMlKemkeyGetValue(k: c_key, pbDst: *mut u8, cbDst: size_t, format: c_format, flags: u32) -> MLKEM_ERROR {
    let mut k = unsafe { Box::from_raw(k) };
    let dst = unsafe { std::slice::from_raw_parts_mut(pbDst, cbDst) };
    let r = crate::mlkem::SymCryptMlKemkeyGetValue(&mut (*k), dst, format.try_into()?, flags);
    // Note: we probably (check) need this to prevent Drop from being called.
    let _ = Box::into_raw(k);
    r
}

#[no_mangle] pub extern "C"
fn SymCryptMlKemEncapsulate(k: c_key, pbAgreedSecret: *mut u8, cbAgreedSecret: size_t,
    pbCiphertext: *mut u8, cbCiphertext: size_t) -> MLKEM_ERROR
{
    let mut k = unsafe { Box::from_raw(k) };
    let agreedSecret = unsafe { std::slice::from_raw_parts_mut(pbAgreedSecret, cbAgreedSecret) };
    let ciphertext = unsafe { std::slice::from_raw_parts_mut(pbCiphertext, cbCiphertext) };
    let r = crate::mlkem::SymCryptMlKemEncapsulate(&mut (*k), agreedSecret, ciphertext);
    // Note: we probably (check) need this to prevent Drop from being called.
    let _ = Box::into_raw(k);
    r
}

#[no_mangle] pub extern "C"
fn SymCryptMlKemEncapsulateEx(k: c_key,
    pbRandom: *mut u8, cbRandom: size_t,
    pbAgreedSecret: *mut u8, cbAgreedSecret: size_t,
    pbCiphertext: *mut u8, cbCiphertext: size_t) -> MLKEM_ERROR
{
    let mut k = unsafe { Box::from_raw(k) };
    let random = unsafe { std::slice::from_raw_parts_mut(pbRandom, cbRandom) };
    let agreedSecret = unsafe { std::slice::from_raw_parts_mut(pbAgreedSecret, cbAgreedSecret) };
    let ciphertext = unsafe { std::slice::from_raw_parts_mut(pbCiphertext, cbCiphertext) };
    let r = crate::mlkem::SymCryptMlKemEncapsulateEx(&mut (*k), random, agreedSecret, ciphertext);
    // Note: we probably (check) need this to prevent Drop from being called.
    let _ = Box::into_raw(k);
    r
}

#[no_mangle] pub extern "C"
fn SymCryptMlKemDecapsulate(k: c_key,
    pbCiphertext: *const u8, cbCiphertext: size_t,
    pbAgreedSecret: *mut u8, cbAgreedSecret: size_t,
    ) -> MLKEM_ERROR
{
    let mut k = unsafe { Box::from_raw(k) };
    let agreedSecret = unsafe { std::slice::from_raw_parts_mut(pbAgreedSecret, cbAgreedSecret) };
    let ciphertext = unsafe { std::slice::from_raw_parts(pbCiphertext, cbCiphertext) };
    let r = crate::mlkem::SymCryptMlKemDecapsulate(&mut (*k), ciphertext, agreedSecret);
    // Note: we probably (check) need this to prevent Drop from being called.
    let _ = Box::into_raw(k);
    r
}

#[no_mangle] pub extern "C"
fn SymCryptMlKemSelftest() {
    println!("SELF-TEST: DOING NOTHING");
}
