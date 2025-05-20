#include <stdlib.h>

#include <symcrypt.h>
#include <symcrypt_internal.h>

#pragma once

const size_t symcrust_hash_SHA3_512_RESULT_SIZE = SYMCRYPT_SHA3_512_RESULT_SIZE;

typedef union {
  struct SYMCRYPT_SHA3_512_STATE sha3_512;
  struct SYMCRYPT_SHAKE128_STATE shake128;
} symcrust_hash_HashState;

extern symcrust_hash_HashState = { .sha3_512 = { 0 } };
