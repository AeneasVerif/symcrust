// Note (Rust): SymCrypt relies on its callers stack-allocating the various states, so we need to
// reveal the definition of the various shake and sha3 states.
// Note (Rust) fortunately, it turns out that these are all the same under the hood. This fact is
// not revealed to clients of SymCrypt, but since we are an internal client, we can leverage that
// and save the need for a tagged union in Rust.

// Previously, was:
/*union HashStateUnion {
    shake128State: shake128State,
    shake256State: shake256State,
    sha3_256State: sha3_256State,
    sha3_512State: sha3_512State,
}*/

#[repr(C)]
struct 
KECCAK_STATE
{
    state: [u64; 25],      // state for Keccak-f[1600] permutation
    inputBlockSize: u32, // rate
    stateIndex: u32,     // position in the state for next merge/extract operation
    paddingValue: u8,   // Keccak padding value
    squeezeMode: bool,    // denotes whether the state is in squeeze mode
}

#[repr(C)]
pub(crate)
struct HASH_STATE {
    state: KECCAK_STATE,
    magic: usize,
}

const SYMCRYPT_SHAKE128_RESULT_SIZE: usize = 32;
const SYMCRYPT_SHAKE128_INPUT_BLOCK_SIZE: usize = 168;

const SYMCRYPT_SHAKE256_RESULT_SIZE: usize = 64;
const SYMCRYPT_SHAKE256_INPUT_BLOCK_SIZE: usize = 136;

extern "C" {
    fn SymCryptShake128Default(pbData: *const u8, cbData: usize, pbResult: &mut [u8; SYMCRYPT_SHAKE128_RESULT_SIZE]);
    fn SymCryptShake128(pbData: *const u8, cbData: usize, pbResult: *mut u8, cbResult: usize);
    fn SymCryptShake128Init(pState: &mut HASH_STATE);
    fn SymCryptShake128Append(pState: &mut HASH_STATE, pbData: *const u8, cbData: usize);
    fn SymCryptShake128Extract(pState: &mut HASH_STATE, pbResult: *mut u8, cbResult: usize, bWipe: bool);
    fn SymCryptShake128Result(pState: &mut HASH_STATE, pbResult: &mut [u8; SYMCRYPT_SHAKE128_RESULT_SIZE]);
    fn SymCryptShake128StateCopy(pSrc: & HASH_STATE, pDst: &mut HASH_STATE);

    fn SymCryptShake256Default(pbData: *const u8, cbData: usize, pbResult: &mut [u8; SYMCRYPT_SHAKE256_RESULT_SIZE]);
    fn SymCryptShake256(pbData: *const u8, cbData: usize, pbResult: *mut u8, cbResult: usize);
    fn SymCryptShake256Init(pState: &mut HASH_STATE);
    fn SymCryptShake256Append(pState: &mut HASH_STATE, pbData: *const u8, cbData: usize);
    fn SymCryptShake256Extract(pState: &mut HASH_STATE, pbResult: *mut u8, cbResult: usize, bWipe: bool);
    fn SymCryptShake256Result(pState: &mut HASH_STATE, pbResult: &mut [u8; SYMCRYPT_SHAKE256_RESULT_SIZE]);
    fn SymCryptShake256StateCopy(pSrc: & HASH_STATE, pDst: &mut HASH_STATE);
}

pub(crate) fn shake128_default(data: &[u8], dst: &mut [u8; SYMCRYPT_SHAKE128_RESULT_SIZE]) {
    unsafe {
        SymCryptShake128Default(data.as_ptr(), data.len(), dst);
    }
}

pub(crate) fn shake128(pbData: &[u8], pbResult: &mut [u8]) {
    unsafe {
        SymCryptShake128(pbData.as_ptr(), pbData.len(), pbResult.as_mut_ptr(), pbResult.len());
    }
}

pub(crate) fn shake128_init(pState: &mut HASH_STATE) {
    unsafe {
        SymCryptShake128Init(pState)
    }
}

pub(crate) fn shake128_append(pState: &mut HASH_STATE, pbData: &[u8]) {
    unsafe {
        SymCryptShake128Append(pState, pbData.as_ptr(), pbData.len());
    }
}

pub(crate) fn shake128_extract(st: &mut HASH_STATE, dst: &mut [u8], wipe: bool) {
    unsafe {
        SymCryptShake128Extract(st, dst.as_mut_ptr(), dst.len(), wipe);
    }
}

pub(crate) fn shake128_result(pState: &mut HASH_STATE, pbResult: &mut [u8; SYMCRYPT_SHAKE128_RESULT_SIZE]) {
    unsafe {
        SymCryptShake128Result(pState, pbResult);
    }
}

pub(crate) fn shake128_state_copy(pSrc: & HASH_STATE, pDst: &mut HASH_STATE) {
    unsafe {
        SymCryptShake128StateCopy(pSrc, pDst);
    }
}

pub(crate) fn shake256_default(data: &[u8], dst: &mut [u8; SYMCRYPT_SHAKE256_RESULT_SIZE]) {
    unsafe {
        SymCryptShake256Default(data.as_ptr(), data.len(), dst);
    }
}

pub(crate) fn shake256(pbData: &[u8], pbResult: &mut [u8]) {
    unsafe {
        SymCryptShake256(pbData.as_ptr(), pbData.len(), pbResult.as_mut_ptr(), pbResult.len());
    }
}

pub(crate) fn shake256_init(pState: &mut HASH_STATE) {
    unsafe {
        SymCryptShake256Init(pState)
    }
}

pub(crate) fn shake256_append(pState: &mut HASH_STATE, pbData: &[u8]) {
    unsafe {
        SymCryptShake256Append(pState, pbData.as_ptr(), pbData.len());
    }
}

pub(crate) fn shake256_extract(st: &mut HASH_STATE, dst: &mut [u8], wipe: bool) {
    unsafe {
        SymCryptShake256Extract(st, dst.as_mut_ptr(), dst.len(), wipe);
    }
}

pub(crate) fn shake256_result(pState: &mut HASH_STATE, pbResult: &mut [u8; SYMCRYPT_SHAKE256_RESULT_SIZE]) {
    unsafe {
        SymCryptShake256Result(pState, pbResult);
    }
}

pub(crate) fn shake256_state_copy(pSrc: & HASH_STATE, pDst: &mut HASH_STATE) {
    unsafe {
        SymCryptShake256StateCopy(pSrc, pDst);
    }
}
