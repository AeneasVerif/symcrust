/* This file is hand-written and implements the "extern" stubs found in
 * c/internal/symcrust_hash.h. It includes c/internal/symcrust_hash.h to make
 * sure the declarations are consistent with the expected signatures.  */

#include <stdlib.h>
#include <symcrypt.h>

#include "internal/symcrust_hash.h"

size_t SYMCRUST_HASH_SHA3_512_RESULT_SIZE = SYMCRYPT_SHA3_512_RESULT_SIZE;

symcrust_hash_HashState SYMCRUST_HASH_UNINITIALIZED_HASH_STATE = { 0 };
