/* This file is hand-written and implements the types found in c/internal/symcrust_hash.h -- it is
 * included from c/internal/symcrust_hash.h */

#pragma once

#include <stdlib.h>
#include <symcrypt.h>

typedef union {
  SYMCRYPT_SHA3_512_STATE sha3_512;
  SYMCRYPT_SHA3_256_STATE sha3_256;
  SYMCRYPT_SHAKE128_STATE shake128;
  SYMCRYPT_SHAKE256_STATE shake256;
} symcrust_hash_HashState;
