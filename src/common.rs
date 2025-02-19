// FIXME: move this into a shared set of definitions, rename to SYMCRYPT_ERROR

#[derive(PartialEq, Debug)]
#[repr(C)]
pub
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

impl std::fmt::Display for MLKEM_ERROR {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

impl std::error::Error for MLKEM_ERROR {}

// #[cfg(not(feature = "dynamic"))]
// extern "C" {
//     fn SymCryptCallbackRandom(pbBuffer: *mut u8, cbBuffer: usize) -> MLKEM_ERROR;
// }

// #[cfg(feature = "dynamic")]
extern "C" {
    fn SymCryptRandom(pbBuffer: *mut u8, cbBuffer: usize);
    fn SymCryptModuleInit(api: u32, minor: u32);
}

pub(crate)
fn callback_random(dst: &mut [u8]) -> MLKEM_ERROR {
    // #[cfg(not(feature = "dynamic"))]
    // unsafe {
    //     SymCryptCallbackRandom(dst.as_mut_ptr(), dst.len())
    // }
    // #[cfg(feature = "dynamic")]
    unsafe {
        SymCryptRandom(dst.as_mut_ptr(), dst.len());
        MLKEM_ERROR::NO_ERROR
    }
}

pub(crate)
fn init() {
    unsafe {
        SymCryptModuleInit(103, 8);
    }
}
