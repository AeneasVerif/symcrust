#include <inttypes.h>
#include <stdlib.h>
#include <stdio.h>
#include <symcrypt.h>

#include "symcrust_mlkem.h"

const uint8_t key_generation_seed[64] = {
  0x7c, 0x99, 0x35, 0xa0, 0xb0, 0x76, 0x94, 0xaa, 0x0c, 0x6d, 0x10, 0xe4, 0xdb,
  0x6b, 0x1a, 0xdd, 0x2f, 0xd8, 0x1a, 0x25, 0xcc, 0xb1, 0x48, 0x03, 0x2d, 0xcd,
  0x73, 0x99, 0x36, 0x73, 0x7f, 0x2d, 0x86, 0x26, 0xed, 0x79, 0xd4, 0x51, 0x14,
  0x08, 0x00, 0xe0, 0x3b, 0x59, 0xb9, 0x56, 0xf8, 0x21, 0x0e, 0x55, 0x60, 0x67,
  0x40, 0x7d, 0x13, 0xdc, 0x90, 0xfa, 0x9e, 0x8b, 0x87, 0x2b, 0xfb, 0x8f
};

int main() {
  SymCryptModuleInit(103, 8);

  core_result_Result_67 k = symcrust_key_key_allocate2(symcrust_key_Params_MlKem768);
  symcrust_common_Error r = symcrust_mlkem_key_set_value(
      ((Eurydice_slice){ .ptr = (void*)key_generation_seed, .len = 64 }),
      symcrust_key_Format_PrivateSeed,
      0, k.val.case_Ok);
  if (r) {
    fprintf(stderr, "Error setting value: %d\n", r);
    exit(1);
  }


/*   // Read secret (a.k.a. decapsulation) key */
/*   let mut secret_key = [0u8; crate::mlkem::sizeof_format_decapsulation_key(3)]; */
/*   let r = crate::mlkem::key_get_value(&k, &mut secret_key, crate::key::Format::DecapsulationKey, 0); */
/*   if r != Error::NoError { */
/*       return Err(Box::new(r)) */
/*   } */
/*   let sha3_256_hash_of_secret_key = hex::decode("7deef44965b03d76de543ad6ef9e74a2772fa5a9fa0e761120dac767cf0152ef")?; */
/*   let mut actual_sha3_256_hash_of_secret_key = [0u8; 32]; */
/*   crate::hash::sha3_256(&secret_key, &mut actual_sha3_256_hash_of_secret_key); */
/*   assert_eq!(sha3_256_hash_of_secret_key, actual_sha3_256_hash_of_secret_key); */

/*   // Read public (a.k.a. encapsulation) key */
/*   let mut public_key = [0u8; crate::mlkem::sizeof_format_encapsulation_key(3)]; */
/*   let r = crate::mlkem::key_get_value(&k, &mut public_key, crate::key::Format::EncapsulationKey, 0); */
/*   if r != Error::NoError { */
/*       return Err(Box::new(r)) */
/*   } */
/*   let sha3_256_hash_of_public_key = hex::decode("f57262661358cde8d3ebf990e5fd1d5b896c992ccfaadb5256b68bbf5943b132")?; */
/*   let mut actual_sha3_256_hash_of_public_key = [0u8; 32]; */
/*   crate::hash::sha3_256(&public_key, &mut actual_sha3_256_hash_of_public_key); */
/*   assert_eq!(sha3_256_hash_of_public_key, actual_sha3_256_hash_of_public_key); */

/*   // Compute shared secret + ciphertext */
/*   let encapsulation_seed = hex::decode("147c03f7a5bebba406c8fae1874d7f13c80efe79a3a9a874cc09fe76f6997615")?; */
/*   let mut actual_shared_secret = [0u8; 32]; */
/*   let mut cipher_text = [0u8; 1088]; */
/*   let r = crate::mlkem::encapsulate_ex(&mut k, &encapsulation_seed, &mut actual_shared_secret, &mut cipher_text); */
/*   if r != Error::NoError { */
/*       return Err(Box::new(r)) */
/*   } */
/*   let sha3_256_hash_of_ciphertext = hex::decode("6e777e2cf8054659136a971d9e70252f301226930c19c470ee0688163a63c15b")?; */
/*   let mut actual_sha3_256_hash_of_ciphertext = [0u8; 32]; */
/*   crate::hash::sha3_256(&cipher_text, &mut actual_sha3_256_hash_of_ciphertext); */
/*   assert_eq!(sha3_256_hash_of_ciphertext, actual_sha3_256_hash_of_ciphertext); */
/*   let shared_secret = hex::decode("e7184a0975ee3470878d2d159ec83129c8aec253d4ee17b4810311d198cd0368")?; */
/*   assert_eq!(shared_secret, actual_shared_secret); */

/*   // Exercise decapsulation, and assert consistency */
/*   let mut shared_secret2 = [0u8; 32]; */
/*   let r = crate::mlkem::decapsulate(&mut k, &cipher_text, &mut shared_secret2); */
/*   if r != Error::NoError { */
/*       return Err(Box::new(r)) */
/*   } */
/*   assert_eq!(shared_secret2, actual_shared_secret); */

/*   // Functional test -- should roundtrip! */
/*   let mut k = crate::key::key_allocate(crate::key::Params::MlKem768)?; */
/*   crate::mlkem::key_generate(&mut k, 0); */
/*   let mut secret = [0u8; 32]; */
/*   let mut cipher = [0u8; 1088]; */
/*   crate::mlkem::encapsulate(&mut k, &mut secret, &mut cipher); */

/*   let mut secret2 = [0u8; 32]; */
/*   crate::mlkem::decapsulate(&mut k, &cipher, &mut secret2); */
/*   assert_eq!(secret, secret2); */

/*   // Perf test -- simplistic */
/*   let mut k = crate::key::key_allocate(crate::key::Params::MlKem768)?; */
/*   for i in 0..1000u32 { */
/*       crate::mlkem::key_generate(&mut k, 0); */
/*       let mut secret = [(i % 256) as u8; 32]; */
/*       let mut cipher = [0u8; 1088]; */
/*       crate::mlkem::encapsulate(&mut k, &mut secret, &mut cipher); */

/*       let mut secret2 = [(i % 256) as u8; 32]; */
/*       crate::mlkem::decapsulate(&mut k, &cipher, &mut secret2); */
/*       assert_eq!(secret, secret2); */
/*   } */


  return 0;
}
