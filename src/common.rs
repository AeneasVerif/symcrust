// FIXME: move this into a shared set of definitions, rename to SYMCRYPT_ERROR
#[derive(PartialEq)]
pub(crate)
// FIXME: make sure constants have values consistent with the C header
enum MLKEM_ERROR {
    NO_ERROR,
    INVALID_BLOB,
    OUT_OF_MEMORY,
    INVALID_ARGUMENT,
    MEMORY_ALLOCATION_FAILURE,
    WRONG_KEY_SIZE,
    INCOMPATIBLE_FORMAT
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
