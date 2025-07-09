/* This file is hand-written and implements the "extern" stubs found in
 * c/internal/symcrust_hash.h. It includes c/internal/symcrust_hash.h to make
 * sure the declarations are consistent with the expected signatures.  */

#include <stdlib.h>
#include <symcrypt.h>

#include "internal/symcrust_hash.h"

symcrust_hash_HashState SYMCRUST_HASH_UNINITIALIZED_HASH_STATE = { 0 };

// SHA3-256

void symcrust_hash_sha3_256_append(symcrust_hash_HashState *p_state,
                                          Eurydice_slice pb_data) {
  SymCryptSha3_256Append(&p_state->sha3_256, pb_data.ptr, pb_data.len);
}

void symcrust_hash_sha3_256_init(symcrust_hash_HashState *p_state) {
  SymCryptSha3_256Init(&p_state->sha3_256);
}

void symcrust_hash_sha3_256_result(symcrust_hash_HashState *p_state,
                                          uint8_t *pb_result) {
  SymCryptSha3_256Result(&p_state->sha3_256, pb_result);
}

// SHA3-512

size_t SYMCRUST_HASH_SHA3_512_RESULT_SIZE = SYMCRYPT_SHA3_512_RESULT_SIZE;

void symcrust_hash_sha3_512(Eurydice_slice pb_data, uint8_t *pb_result) {
  SymCryptSha3_512(pb_data.ptr, pb_data.len, pb_result);
}

void symcrust_hash_sha3_512_append(symcrust_hash_HashState *p_state,
                                          Eurydice_slice pb_data) {
  SymCryptSha3_512Append(&p_state->sha3_512, pb_data.ptr, pb_data.len);
}

void symcrust_hash_sha3_512_init(symcrust_hash_HashState *p_state) {
  SymCryptSha3_512Init(&p_state->sha3_512);
}

void symcrust_hash_sha3_512_result(symcrust_hash_HashState *p_state,
                                          uint8_t *pb_result) {
  SymCryptSha3_512Result(&p_state->sha3_512, pb_result);
}

// SHAKE128

void symcrust_hash_shake128_append(symcrust_hash_HashState *p_state,
                                          Eurydice_slice pb_data) {
  SymCryptShake128Append(&p_state->shake128, pb_data.ptr, pb_data.len);
}

void symcrust_hash_shake128_extract(symcrust_hash_HashState *st,
                                           Eurydice_slice dst, bool wipe) {
  SymCryptShake128Extract(&st->shake128, dst.ptr, dst.len, wipe);
}

void symcrust_hash_shake128_init(symcrust_hash_HashState *p_state) {
  SymCryptShake128Init(&p_state->shake128);
}

void symcrust_hash_shake128_state_copy(symcrust_hash_HashState *p_src,
                                              symcrust_hash_HashState *p_dst) {
  SymCryptShake128StateCopy(&p_src->shake128, &p_dst->shake128);
}

// SHAKE256

void symcrust_hash_shake256_append(symcrust_hash_HashState *p_state,
                                          Eurydice_slice pb_data) {
  SymCryptShake256Append(&p_state->shake256, pb_data.ptr, pb_data.len);
}

void symcrust_hash_shake256_extract(symcrust_hash_HashState *st,
                                           Eurydice_slice dst, bool wipe) {
  SymCryptShake256Extract(&st->shake256, dst.ptr, dst.len, wipe);
}

void symcrust_hash_shake256_init(symcrust_hash_HashState *p_state) {
  SymCryptShake256Init(&p_state->shake256);
}

void symcrust_hash_shake256_state_copy(symcrust_hash_HashState *p_src,
                                              symcrust_hash_HashState *p_dst) {
  SymCryptShake256StateCopy(&p_src->shake256, &p_dst->shake256);
}
