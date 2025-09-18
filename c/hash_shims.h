#pragma once

#include <stdlib.h>

#include <symcrypt.h>

size_t symcrust_hash_SHA3_512_RESULT_SIZE = SYMCRYPT_SHA3_512_RESULT_SIZE;

typedef union {
  SYMCRYPT_SHA3_512_STATE sha3_512;
  SYMCRYPT_SHAKE128_STATE shake128;
} symcrust_hash_HashState;

symcrust_hash_HashState symcrust_hash_UNINITIALIZED_HASH_STATE = { 0 };
