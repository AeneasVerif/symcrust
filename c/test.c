#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>
#include <symcrypt.h>

#include "symcrust_mlkem.h"

const unsigned char key_generation_seed[] = {
    0x7c, 0x99, 0x35, 0xa0, 0xb0, 0x76, 0x94, 0xaa, 0x0c, 0x6d, 0x10,
    0xe4, 0xdb, 0x6b, 0x1a, 0xdd, 0x2f, 0xd8, 0x1a, 0x25, 0xcc, 0xb1,
    0x48, 0x03, 0x2d, 0xcd, 0x73, 0x99, 0x36, 0x73, 0x7f, 0x2d, 0x86,
    0x26, 0xed, 0x79, 0xd4, 0x51, 0x14, 0x08, 0x00, 0xe0, 0x3b, 0x59,
    0xb9, 0x56, 0xf8, 0x21, 0x0e, 0x55, 0x60, 0x67, 0x40, 0x7d, 0x13,
    0xdc, 0x90, 0xfa, 0x9e, 0x8b, 0x87, 0x2b, 0xfb, 0x8f,
};

const unsigned char expected_sha3_256_hash_of_secret_key[] = {
    0x7d, 0xee, 0xf4, 0x49, 0x65, 0xb0, 0x3d, 0x76, 0xde, 0x54, 0x3a,
    0xd6, 0xef, 0x9e, 0x74, 0xa2, 0x77, 0x2f, 0xa5, 0xa9, 0xfa, 0x0e,
    0x76, 0x11, 0x20, 0xda, 0xc7, 0x67, 0xcf, 0x01, 0x52, 0xef,
};

const unsigned char expected_sha3_256_hash_of_public_key[] = {
    0xf5, 0x72, 0x62, 0x66, 0x13, 0x58, 0xcd, 0xe8, 0xd3, 0xeb, 0xf9,
    0x90, 0xe5, 0xfd, 0x1d, 0x5b, 0x89, 0x6c, 0x99, 0x2c, 0xcf, 0xaa,
    0xdb, 0x52, 0x56, 0xb6, 0x8b, 0xbf, 0x59, 0x43, 0xb1, 0x32,
};

const unsigned char encapsulation_seed[] = {
    0x14, 0x7c, 0x03, 0xf7, 0xa5, 0xbe, 0xbb, 0xa4, 0x06, 0xc8, 0xfa,
    0xe1, 0x87, 0x4d, 0x7f, 0x13, 0xc8, 0x0e, 0xfe, 0x79, 0xa3, 0xa9,
    0xa8, 0x74, 0xcc, 0x09, 0xfe, 0x76, 0xf6, 0x99, 0x76, 0x15,
};

const unsigned char expected_sha3_256_hash_of_ciphertext[] = {
    0x6e, 0x77, 0x7e, 0x2c, 0xf8, 0x05, 0x46, 0x59, 0x13, 0x6a, 0x97,
    0x1d, 0x9e, 0x70, 0x25, 0x2f, 0x30, 0x12, 0x26, 0x93, 0x0c, 0x19,
    0xc4, 0x70, 0xee, 0x06, 0x88, 0x16, 0x3a, 0x63, 0xc1, 0x5b,
};

const unsigned char expected_shared_secret[] = {
    0xe7, 0x18, 0x4a, 0x09, 0x75, 0xee, 0x34, 0x70, 0x87, 0x8d, 0x2d,
    0x15, 0x9e, 0xc8, 0x31, 0x29, 0xc8, 0xae, 0xc2, 0x53, 0xd4, 0xee,
    0x17, 0xb4, 0x81, 0x03, 0x11, 0xd1, 0x98, 0xcd, 0x03, 0x68,
};

#define CHECK_ERROR(r, msg) \
  do { \
    if (r != symcrust_common_Error_NoError) { \
      printf(msg " failed %d\n", r); \
      exit(1); \
    } \
  } while (0)

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
      if (actual[i] != expected[i] && index == SIZE_T_MAX)
        index = i;
    }
    printf("\n");

    printf("actual and expected differ at byte %zu\n", index);
    exit(1);
  }
}

#define SLICE(ptr_, len_) ((Eurydice_slice){ .ptr = (void*)(ptr_), .len = len_ })

int main() {
  SymCryptModuleInit(103, 8);

  // Allocate + key-gen
  core_result_Result_67 k_result = symcrust_key_key_allocate2(symcrust_key_Params_MlKem768);
  symcrust_common_Error r = symcrust_mlkem_key_set_value(
      SLICE(key_generation_seed, 64),
      symcrust_key_Format_PrivateSeed,
      0, k_result.val.case_Ok);
  CHECK_ERROR(r, "setvalue");

  Eurydice_dst_8c k = k_result.val.case_Ok;

  // Read secret (a.k.a. decapsulation) key
  unsigned char secret_key[2400] = { 0 };
  r = symcrust_mlkem_key_get_value(k, SLICE(secret_key, sizeof(secret_key)),
                                   symcrust_key_Format_DecapsulationKey, 0);
  CHECK_ERROR(r, "getvalue (decaps)");

  unsigned char sha3_256_hash_of_secret_key[32];
  SymCryptSha3_256(secret_key, sizeof(secret_key), sha3_256_hash_of_secret_key);
  compare_or_fail(sha3_256_hash_of_secret_key, expected_sha3_256_hash_of_secret_key, 32);

  // Read public (a.k.a. encapsulation) key
  unsigned char public_key[1184] = { 0 };
  r = symcrust_mlkem_key_get_value(k, SLICE(public_key, sizeof(public_key)),
                               symcrust_key_Format_EncapsulationKey, 0);
  CHECK_ERROR(r, "getvalue (encaps)");
  unsigned char sha3_256_hash_of_public_key[32];
  SymCryptSha3_256(public_key, sizeof(public_key), sha3_256_hash_of_public_key);
  compare_or_fail(sha3_256_hash_of_public_key, expected_sha3_256_hash_of_public_key, 32);

  // Compute shared secret + ciphertext
  unsigned char ciphertext[1088] = { 0 }, shared_secret[32] = { 0 };
  r = symcrust_mlkem_encapsulate_ex(
      k, SLICE(encapsulation_seed, sizeof(encapsulation_seed)), SLICE(shared_secret, sizeof(shared_secret)),
      SLICE(ciphertext, sizeof(ciphertext)));
  CHECK_ERROR(r, "encapsulate");
  unsigned char sha3_256_hash_of_ciphertext[32];
  SymCryptSha3_256(ciphertext, sizeof(ciphertext), sha3_256_hash_of_ciphertext);
  compare_or_fail(sha3_256_hash_of_ciphertext, expected_sha3_256_hash_of_ciphertext, 32);
  compare_or_fail(shared_secret, expected_shared_secret, 32);

  // Exercise decapsulation, and assert consistency
  unsigned char shared_secret2[32] = { 0 };
  symcrust_mlkem_decapsulate(k, SLICE(ciphertext, sizeof(ciphertext)), SLICE(shared_secret2, sizeof(shared_secret2)));
  compare_or_fail(shared_secret2, expected_shared_secret, 32);

  printf("done\n");

  return 0;
}
