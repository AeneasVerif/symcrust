#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdio.h>
#include "symcrypt.h"

#define CHECK_ERROR(r, msg) \
  do { \
    if (r != SYMCRYPT_NO_ERROR) { \
      printf(msg " failed\n"); \
      exit(1); \
    } \
  } while (0)


const unsigned char key_generation_seed[] = {
    0x7c, 0x99, 0x35, 0xa0, 0xb0, 0x76, 0x94, 0xaa, 0x0c, 0x6d, 0x10,
    0xe4, 0xdb, 0x6b, 0x1a, 0xdd, 0x2f, 0xd8, 0x1a, 0x25, 0xcc, 0xb1,
    0x48, 0x03, 0x2d, 0xcd, 0x73, 0x99, 0x36, 0x73, 0x7f, 0x2d, 0x86,
    0x26, 0xed, 0x79, 0xd4, 0x51, 0x14, 0x08, 0x00, 0xe0, 0x3b, 0x59,
    0xb9, 0x56, 0xf8, 0x21, 0x0e, 0x55, 0x60, 0x67, 0x40, 0x7d, 0x13,
    0xdc, 0x90, 0xfa, 0x9e, 0x8b, 0x87, 0x2b, 0xfb, 0x8f,
};

const unsigned char expected_sha3_256_hash_of_public_key[] = {
    0x7d, 0xee, 0xf4, 0x49, 0x65, 0xb0, 0x3d, 0x76, 0xde, 0x54, 0x3a,
    0xd6, 0xef, 0x9e, 0x74, 0xa2, 0x77, 0x2f, 0xa5, 0xa9, 0xfa, 0x0e,
    0x76, 0x11, 0x20, 0xda, 0xc7, 0x67, 0xcf, 0x01, 0x52, 0xef,
};

void compare_or_fail(const unsigned char *actual, const unsigned char *expected, size_t sz) {
  if (memcmp(actual, expected, sz)) {
    printf("actual:   ");
    for (size_t i = 0; i < sz; ++i) {
      printf("%02x", actual[i]);
    }
    printf("\n");

    size_t index = SIZE_T_MAX;

    printf("expected: ");
    for (size_t i = 0; i < sz; ++i) {
      printf("%02x", expected[i]);
      if (actual[i] != expected[i] && index != SIZE_T_MAX)
        index = i;
    }
    printf("\n");

    printf("actual and expected differ at byte %zu\n", index);
  }
}

int main() {
  PSYMCRYPT_MLKEMKEY k =
      SymCryptMlKemkeyAllocate(SYMCRYPT_MLKEM_PARAMS_MLKEM768);
  SYMCRYPT_ERROR r =
      SymCryptMlKemkeySetValue(key_generation_seed, sizeof(key_generation_seed),
                               SYMCRYPT_MLKEMKEY_FORMAT_PRIVATE_SEED, 0, k);
  CHECK_ERROR(r, "setvalue");

  unsigned char secret_key[2400] = { 0 };
  r = SymCryptMlKemkeyGetValue(k, secret_key, sizeof(secret_key),
                               SYMCRYPT_MLKEMKEY_FORMAT_DECAPSULATION_KEY, 0);
  CHECK_ERROR(r, "getvalue");

  unsigned char sha3_256_hash_of_secret_key[32];
  SymCryptSha3_256(secret_key, sizeof(secret_key), sha3_256_hash_of_secret_key);

  compare_or_fail(sha3_256_hash_of_secret_key, expected_sha3_256_hash_of_public_key, 32);

  printf("done\n");
}
