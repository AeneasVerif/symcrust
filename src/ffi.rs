// This module contains reverse-bindings that expose our Rust implementations with a C ABI,
// identical to that exposed in symcrypt.h
//
// The primary goal of this module is to expose just enough functions that the unit test can run
// performance benchmarks on our Rust implementation.
//
// SymCrypt enforces abstraction by using an incomplete struct type for the PMLKEMKEY object,
// and the test driver uses only the public API, meaning we can lie and use another (Rust) type for
// the key as long as it's behind a pointer.

use crate::common::Error;
use libc::{c_int, size_t};

// TYPE DEFINITIONS
// ----------------

// C11 enums are `int`, per the C standard
type CParams = c_int;
type CFormat = c_int;

// So the dynamically-sized type (DST) comes back to bite us. The KEY type is a DST, meaning that
// in Rust it's a fat pointer -- it does not implement the Thin trait, and as such cannot be passed
// via the FFI. We add another layer of indirection.
type CKey = *mut Box<crate::key::Key>;

// We could, however, decompose it into raw parts:
// https://doc.rust-lang.org/std/primitive.pointer.html#method.to_raw_parts and, in the FFI layer,
// query the ML-KEM variant to deduce the size of the underlying allocation and reconstruct the
// fat pointer.

// CONVERSIONS
// -----------

impl TryFrom<c_int> for crate::key::Params {
    type Error = Error;
    fn try_from(params: c_int) -> Result<crate::key::Params, Error> {
        match params {
            0 => Result::Err(Error::IncompatibleFormat),
            1 => Result::Ok(crate::key::Params::MlKem512),
            2 => Result::Ok(crate::key::Params::MlKem768),
            3 => Result::Ok(crate::key::Params::MlKem1024),
            _ => Result::Err(Error::InvalidArgument),
        }
    }
}

impl TryFrom<c_int> for crate::key::Format {
    type Error = Error;
    fn try_from(format: c_int) -> Result<crate::key::Format, Error> {
        match format {
            0 => Result::Err(Error::IncompatibleFormat),
            1 => Result::Ok(crate::key::Format::PrivateSeed),
            2 => Result::Ok(crate::key::Format::DecapsulationKey),
            3 => Result::Ok(crate::key::Format::EncapsulationKey),
            _ => Result::Err(Error::InvalidArgument),
        }
    }
}

// API
// ---

#[no_mangle]
pub extern "C" fn SymCryptMlKemkeyAllocate(params: c_int) -> CKey {
    match crate::key::Params::try_from(params) {
        Result::Err(_) => std::ptr::null_mut(),
        Result::Ok(params) => match crate::key::key_allocate(params) {
            Result::Err(_) => std::ptr::null_mut(),
            Result::Ok(k) => Box::into_raw(Box::new(k)),
        },
    }
}

#[no_mangle]
pub extern "C" fn SymCryptMlKemkeyFree(k: CKey) {
    let _ = unsafe { Box::from_raw(k) };
    // Drop trait gets called here, presumably.
}

#[no_mangle]
pub extern "C" fn SymCryptMlKemSizeofKeyFormatFromParams(
    params: CParams,
    format: CFormat,
    sz: &mut size_t,
) -> Error {
    *sz = crate::mlkem::sizeof_key_format_from_params(
        params.try_into()?,
        format.try_into()?,
    );
    Error::NoError
}

#[no_mangle]
pub extern "C" fn SymCryptMlKemSizeofCiphertextFromParams(
    params: CParams,
    sz: &mut size_t,
) -> Error {
    *sz = crate::mlkem::sizeof_ciphertext_from_params(params.try_into()?);
    Error::NoError
}

#[no_mangle]
pub extern "C" fn SymCryptMlKemkeyGenerate(k: CKey, flags: u32) -> Error {
    let mut k = unsafe { Box::from_raw(k) };
    // Note: the * can be inserted by Rust automatically
    let r = crate::mlkem::key_generate(&mut (*k), flags);
    // Note: we probably (check) need this to prevent Drop from being called.
    let _ = Box::into_raw(k);
    r
}

#[no_mangle]
pub extern "C" fn SymCryptMlKemkeySetValue(
    pb_src: *const u8,
    cb_src: size_t,
    format: CFormat,
    flags: u32,
    k: CKey,
) -> Error {
    let mut k = unsafe { Box::from_raw(k) };
    let src = unsafe { std::slice::from_raw_parts(pb_src, cb_src) };
    let r = crate::mlkem::key_set_value(src, format.try_into()?, flags, &mut (*k));
    // Note: we probably (check) need this to prevent Drop from being called.
    let _ = Box::into_raw(k);
    r
}

#[no_mangle]
pub extern "C" fn SymCryptMlKemkeyGetValue(
    k: CKey,
    pb_dst: *mut u8,
    cb_dst: size_t,
    format: CFormat,
    flags: u32,
) -> Error {
    let mut k = unsafe { Box::from_raw(k) };
    let dst = unsafe { std::slice::from_raw_parts_mut(pb_dst, cb_dst) };
    let r = crate::mlkem::key_get_value(&mut (*k), dst, format.try_into()?, flags);
    // Note: we probably (check) need this to prevent Drop from being called.
    let _ = Box::into_raw(k);
    r
}

#[no_mangle]
pub extern "C" fn SymCryptMlKemEncapsulate(
    k: CKey,
    pb_agreed_secret: *mut u8,
    cb_agreed_secret: size_t,
    pb_ciphertext: *mut u8,
    cb_ciphertext: size_t,
) -> Error {
    let mut k = unsafe { Box::from_raw(k) };
    let agreed_secret = unsafe { std::slice::from_raw_parts_mut(pb_agreed_secret, cb_agreed_secret) };
    let ciphertext = unsafe { std::slice::from_raw_parts_mut(pb_ciphertext, cb_ciphertext) };
    let r = crate::mlkem::encapsulate(&mut (*k), agreed_secret, ciphertext);
    // Note: we probably (check) need this to prevent Drop from being called.
    let _ = Box::into_raw(k);
    r
}

#[no_mangle]
pub extern "C" fn SymCryptMlKemEncapsulateEx(
    k: CKey,
    pb_random: *mut u8,
    cb_random: size_t,
    pb_agreed_secret: *mut u8,
    cb_agreed_secret: size_t,
    pb_ciphertext: *mut u8,
    cb_ciphertext: size_t,
) -> Error {
    let mut k = unsafe { Box::from_raw(k) };
    let random = unsafe { std::slice::from_raw_parts_mut(pb_random, cb_random) };
    let agreed_secret = unsafe { std::slice::from_raw_parts_mut(pb_agreed_secret, cb_agreed_secret) };
    let ciphertext = unsafe { std::slice::from_raw_parts_mut(pb_ciphertext, cb_ciphertext) };
    let r = crate::mlkem::encapsulate_ex(&mut (*k), random, agreed_secret, ciphertext);
    // Note: we probably (check) need this to prevent Drop from being called.
    let _ = Box::into_raw(k);
    r
}

#[no_mangle]
pub extern "C" fn SymCryptMlKemDecapsulate(
    k: CKey,
    pb_ciphertext: *const u8,
    cb_ciphertext: size_t,
    pb_agreed_secret: *mut u8,
    cb_agreed_secret: size_t,
) -> Error {
    let mut k = unsafe { Box::from_raw(k) };
    let agreed_secret = unsafe { std::slice::from_raw_parts_mut(pb_agreed_secret, cb_agreed_secret) };
    let ciphertext = unsafe { std::slice::from_raw_parts(pb_ciphertext, cb_ciphertext) };
    let r = crate::mlkem::decapsulate(&mut (*k), ciphertext, agreed_secret);
    // Note: we probably (check) need this to prevent Drop from being called.
    let _ = Box::into_raw(k);
    r
}

#[no_mangle]
pub extern "C" fn SymCryptMlKemSelftest() {
    println!("SELF-TEST: DOING NOTHING");
}

// It is not possible to both link to and export a symbol with the same name
// in a generic Rust-y way: https://github.com/rust-lang/rfcs/issues/2771
//
// Instead we export some Sctest functions which correspond to production SymCrypt symbols
#[no_mangle]
pub extern "C" fn SctestModuleInit() {
    crate::common::init();
}

#[no_mangle]
pub extern "C" fn SctestWipe(pb_data: *mut u8, cb_data: usize) {
    crate::common::wipe(pb_data, cb_data);
}