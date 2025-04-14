#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub fn SymCryptSha3_384(pbData: &[u8], cbData: usize, pbResult: &mut [u8])
{
  let mut state: crate::symcrypt_internal::SYMCRYPT_SHA3_384_STATE = Default::default();
  SymCryptSha3_384Init(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHA3_384_STATE>(&mut state)
  );
  SymCryptSha3_384Append(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHA3_384_STATE>(&mut state),
    pbData,
    cbData
  );
  SymCryptSha3_384Result(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHA3_384_STATE>(&mut state),
    pbResult
  )
}

pub fn SymCryptSha3_384Append(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_384_STATE],
  pbData: &[u8],
  cbData: usize
)
{
  crate::sha3::SymCryptKeccakAppend(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE>(
      &mut (pState[0usize]).ks
    ),
    pbData,
    cbData
  )
}

pub fn SymCryptSha3_384Init(pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_384_STATE])
{
  crate::sha3::SymCryptKeccakInit(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE>(
      &mut (pState[0usize]).ks
    ),
    104u32,
    6u8
  )
}

pub fn SymCryptSha3_384Result(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_384_STATE],
  pbResult: &mut [u8]
)
{
  crate::sha3::SymCryptKeccakExtract(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE>(
      &mut (pState[0usize]).ks
    ),
    pbResult,
    48usize,
    1u8
  )
}

pub fn SymCryptSha3_384StateCopy(
  pSrc: &[crate::symcrypt_internal::SYMCRYPT_SHA3_384_STATE],
  pDst: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_384_STATE]
)
{ pDst[0usize] = pSrc[0usize] }

pub const sha3_384KATAnswer: [u8; 48] =
    [236u8, 1u8, 73u8, 130u8, 136u8, 81u8, 111u8, 201u8, 38u8, 69u8, 159u8, 88u8, 226u8, 198u8,
        173u8, 141u8, 249u8, 180u8, 115u8, 203u8, 15u8, 192u8, 140u8, 37u8, 150u8, 218u8, 124u8,
        240u8, 228u8, 155u8, 228u8, 178u8, 152u8, 216u8, 140u8, 234u8, 146u8, 122u8, 199u8, 245u8,
        57u8, 241u8, 237u8, 242u8, 40u8, 55u8, 109u8, 37u8];
