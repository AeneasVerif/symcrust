// FIXME: move this into a shared set of definitions, rename to SYMCRYPT_ERROR
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]

#[derive(PartialEq, Debug)]
#[repr(C)]
pub(crate)
enum MLKEM_ERROR {
    NO_ERROR = 0,
    UNUSED = 0x8000, // Start our error codes here so they're easier to distinguish
    WRONG_KEY_SIZE,
    WRONG_BLOCK_SIZE,
    WRONG_DATA_SIZE,
    WRONG_NONCE_SIZE,
    WRONG_TAG_SIZE,
    WRONG_ITERATION_COUNT,
    AUTHENTICATION_FAILURE,
    EXTERNAL_FAILURE,
    FIPS_FAILURE,
    HARDWARE_FAILURE,
    NOT_IMPLEMENTED,
    INVALID_BLOB,
    BUFFER_TOO_SMALL,
    INVALID_ARGUMENT,
    MEMORY_ALLOCATION_FAILURE,
    SIGNATURE_VERIFICATION_FAILURE,
    INCOMPATIBLE_FORMAT,
    VALUE_TOO_LARGE,
    SESSION_REPLAY_FAILURE,
    HBS_NO_OTS_KEYS_LEFT,
    HBS_PUBLIC_ROOT_MISMATCH,
}

extern "C" {
    fn SymCryptCallbackRandom(pbBuffer: *mut u8, cbBuffer: usize) -> MLKEM_ERROR;
}

pub(crate)
fn callback_random(dst: &mut [u8]) -> MLKEM_ERROR {
    unsafe {
        SymCryptCallbackRandom(dst.as_mut_ptr(), dst.len())
    }
}
