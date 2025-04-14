use crate::symcrypt_internal::*;

const SYMCRYPT_SHA3_256_RESULT_SIZE: usize = 32;

type PSYMCRYPT_SHA3_256_STATE = *mut SYMCRYPT_SHA3_256_STATE;
type PCSYMCRYPT_SHA3_256_STATE = *const SYMCRYPT_SHA3_256_STATE;

#[no_mangle]
pub extern "C" fn SymCryptSha3_256(
    pbData: *const u8,
    cbData: usize,
    pbResult: &mut [u8; SYMCRYPT_SHA3_256_RESULT_SIZE],
) {
    let data = unsafe { std::slice::from_raw_parts(pbData, cbData) };
    crate::sha3_256::SymCryptSha3_256(data, cbData, pbResult)
}

#[no_mangle]
pub extern "C" fn
SymCryptSha3_256Init(pState: PSYMCRYPT_SHA3_256_STATE) {
    let state = unsafe { std::slice::from_raw_parts_mut(pState, 1) };
    crate::sha3_256::SymCryptSha3_256Init(state)
}

#[no_mangle]
pub extern "C" fn
SymCryptSha3_256Append(
    pState: PSYMCRYPT_SHA3_256_STATE,
    pbData: *const u8,
    cbData: usize)
{
    let state = unsafe { std::slice::from_raw_parts_mut(pState, 1) };
    let data = unsafe { std::slice::from_raw_parts(pbData, cbData) };
    crate::sha3_256::SymCryptSha3_256Append(state, data, cbData);
}

#[no_mangle]
pub extern "C" fn
SymCryptSha3_256Result(
    pState: PSYMCRYPT_SHA3_256_STATE,
    pbResult: &mut [u8; SYMCRYPT_SHA3_256_RESULT_SIZE]
) {
    let state = unsafe { std::slice::from_raw_parts_mut(pState, 1) };
    crate::sha3_256::SymCryptSha3_256Result(state, pbResult);
}

#[no_mangle]
pub extern "C" fn
SymCryptSha3_256StateCopy(pSrc: PCSYMCRYPT_SHA3_256_STATE, pDst: PSYMCRYPT_SHA3_256_STATE) {
    let src = unsafe { std::slice::from_raw_parts(pSrc, 1) };
    let dst = unsafe { std::slice::from_raw_parts_mut(pDst, 1) };
    crate::sha3_256::SymCryptSha3_256StateCopy(src, dst);
}
