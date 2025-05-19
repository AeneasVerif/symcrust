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

// Not all of the bindings are used so far -- we leave them for now.
#![allow(dead_code)]

type KeccakState = crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE;

#[repr(C)]
#[repr(align(16))]
pub(crate) union HashState {
    sha3_256_state: crate::symcrypt_internal::SYMCRYPT_SHA3_256_STATE,
    sha3_512_state: crate::symcrypt_internal::SYMCRYPT_SHA3_512_STATE,
    shake128_state: crate::symcrypt_internal::SYMCRYPT_SHAKE128_STATE,
    shake256_state: crate::symcrypt_internal::SYMCRYPT_SHAKE256_STATE,
}

pub(crate) const UNINITIALIZED_HASH_STATE: HashState = HashState {
    sha3_256_state: crate::symcrypt_internal::SYMCRYPT_SHA3_256_STATE {
        ks: crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE {
            state: [0; 25],
            inputBlockSize: 0,
            stateIndex: 0,
            paddingValue: 0,
            squeezeMode: 0,
        },
        magic: 0,
    },
};

pub const SHAKE128_RESULT_SIZE: usize = 32;
pub const SHAKE128_INPUT_BLOCK_SIZE: usize = 168;

pub const SHAKE256_RESULT_SIZE: usize = 64;
pub const SHAKE256_INPUT_BLOCK_SIZE: usize = 136;

pub const SHA3_256_RESULT_SIZE: usize = 32;
pub const SHA3_256_INPUT_BLOCK_SIZE: usize = 136;

pub const SHA3_512_RESULT_SIZE: usize = 64;
pub const SHA3_512_INPUT_BLOCK_SIZE: usize = 72;

// SHAKE128

fn get_shake128(s: &mut HashState) -> &mut [crate::symcrypt_internal::SYMCRYPT_SHAKE128_STATE] {
    std::slice::from_mut(unsafe { &mut s.shake128_state })
}

fn get_shake128_imm(s: &HashState) -> &[crate::symcrypt_internal::SYMCRYPT_SHAKE128_STATE] {
    std::slice::from_ref(unsafe { &s.shake128_state })
}

pub(crate) fn shake128_default(data: &[u8], dst: &mut [u8; SHAKE128_RESULT_SIZE]) {
    crate::shake::SymCryptShake128Default(data, data.len(), dst);
}

pub(crate) fn shake128(pb_data: &[u8], pb_result: &mut [u8]) {
    crate::shake::SymCryptShake128(pb_data, pb_data.len(), pb_result, pb_result.len());
}

pub(crate) fn shake128_init(p_state: &mut HashState) {
    crate::shake::SymCryptShake128Init(get_shake128(p_state))
}

pub(crate) fn shake128_append(p_state: &mut HashState, pb_data: &[u8]) {
    crate::shake::SymCryptShake128Append(get_shake128(p_state), pb_data, pb_data.len());
}

pub(crate) fn shake128_extract(st: &mut HashState, dst: &mut [u8], wipe: bool) {
    crate::shake::SymCryptShake128Extract(get_shake128(st), dst, dst.len(), wipe as u8);
}

pub(crate) fn shake128_result(p_state: &mut HashState, pb_result: &mut [u8; SHAKE128_RESULT_SIZE]) {
    crate::shake::SymCryptShake128Result(get_shake128(p_state), pb_result);
}

pub(crate) fn shake128_state_copy(p_src: &HashState, p_dst: &mut HashState) {
    crate::shake::SymCryptShake128StateCopy(get_shake128_imm(p_src), get_shake128(p_dst));
}

// SHAKE256

fn get_shake256(s: &mut HashState) -> &mut [crate::symcrypt_internal::SYMCRYPT_SHAKE256_STATE] {
    std::slice::from_mut(unsafe { &mut s.shake256_state })
}

fn get_shake256_imm(s: &HashState) -> &[crate::symcrypt_internal::SYMCRYPT_SHAKE256_STATE] {
    std::slice::from_ref(unsafe { &s.shake256_state })
}

pub(crate) fn shake256_default(data: &[u8], dst: &mut [u8; SHAKE256_RESULT_SIZE]) {
    crate::shake::SymCryptShake256Default(data, data.len(), dst);
}

pub(crate) fn shake256(pb_data: &[u8], pb_result: &mut [u8]) {
    crate::shake::SymCryptShake256(pb_data, pb_data.len(), pb_result, pb_result.len());
}

pub(crate) fn shake256_init(p_state: &mut HashState) {
    crate::shake::SymCryptShake256Init(get_shake256(p_state))
}

pub(crate) fn shake256_append(p_state: &mut HashState, pb_data: &[u8]) {
    crate::shake::SymCryptShake256Append(get_shake256(p_state), pb_data, pb_data.len());
}

pub(crate) fn shake256_extract(st: &mut HashState, dst: &mut [u8], wipe: bool) {
    crate::shake::SymCryptShake256Extract(get_shake256(st), dst, dst.len(), wipe as u8);
}

pub(crate) fn shake256_result(p_state: &mut HashState, pb_result: &mut [u8; SHAKE256_RESULT_SIZE]) {
    crate::shake::SymCryptShake256Result(get_shake256(p_state), pb_result);
}

pub(crate) fn shake256_state_copy(p_src: &HashState, p_dst: &mut HashState) {
    crate::shake::SymCryptShake256StateCopy(get_shake256_imm(p_src), get_shake256(p_dst));
}

// SHA3_256

fn get_sha3_256(s: &mut HashState) -> &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_256_STATE] {
    std::slice::from_mut(unsafe { &mut s.sha3_256_state })
}

fn get_sha3_256_imm(s: &HashState) -> &[crate::symcrypt_internal::SYMCRYPT_SHA3_256_STATE] {
    std::slice::from_ref(unsafe { &s.sha3_256_state })
}

pub(crate) fn sha3_256(pb_data: &[u8], pb_result: &mut [u8; SHA3_256_RESULT_SIZE]) {
    crate::sha3_256::SymCryptSha3_256(pb_data, pb_data.len(), pb_result);
}

pub(crate) fn sha3_256_init(p_state: &mut HashState) {
    crate::sha3_256::SymCryptSha3_256Init(get_sha3_256(p_state))
}

pub(crate) fn sha3_256_append(p_state: &mut HashState, pb_data: &[u8]) {
    crate::sha3_256::SymCryptSha3_256Append(get_sha3_256(p_state), pb_data, pb_data.len());
}

pub(crate) fn sha3_256_result(p_state: &mut HashState, pb_result: &mut [u8; SHA3_256_RESULT_SIZE]) {
    crate::sha3_256::SymCryptSha3_256Result(get_sha3_256(p_state), pb_result);
}

pub(crate) fn sha3_256_state_copy(p_src: &HashState, p_dst: &mut HashState) {
    crate::sha3_256::SymCryptSha3_256StateCopy(get_sha3_256_imm(p_src), get_sha3_256(p_dst));
}

// SHA3_512

fn get_sha3_512(s: &mut HashState) -> &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_512_STATE] {
    std::slice::from_mut(unsafe { &mut s.sha3_512_state })
}

fn get_sha3_512_imm(s: &HashState) -> &[crate::symcrypt_internal::SYMCRYPT_SHA3_512_STATE] {
    std::slice::from_ref(unsafe { &s.sha3_512_state })
}

pub(crate) fn sha3_512(pb_data: &[u8], pb_result: &mut [u8; SHA3_512_RESULT_SIZE]) {
    crate::sha3_512::SymCryptSha3_512(pb_data, pb_data.len(), pb_result);
}

pub(crate) fn sha3_512_init(p_state: &mut HashState) {
    crate::sha3_512::SymCryptSha3_512Init(get_sha3_512(p_state))
}

pub(crate) fn sha3_512_append(p_state: &mut HashState, pb_data: &[u8]) {
    crate::sha3_512::SymCryptSha3_512Append(get_sha3_512(p_state), pb_data, pb_data.len());
}

pub(crate) fn sha3_512_result(p_state: &mut HashState, pb_result: &mut [u8; SHA3_512_RESULT_SIZE]) {
    crate::sha3_512::SymCryptSha3_512Result(get_sha3_512(p_state), pb_result);
}

pub(crate) fn sha3_512_state_copy(p_src: &HashState, p_dst: &mut HashState) {
    crate::sha3_512::SymCryptSha3_512StateCopy(get_sha3_512_imm(p_src), get_sha3_512(p_dst));
}
