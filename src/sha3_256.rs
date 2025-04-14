#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub fn SymCryptSha3_256(pbData: &[u8], cbData: usize, pbResult: &mut [u8])
{
  let mut state: crate::symcrypt_internal::SYMCRYPT_SHA3_256_STATE = Default::default();
  SymCryptSha3_256Init(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHA3_256_STATE>(&mut state)
  );
  SymCryptSha3_256Append(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHA3_256_STATE>(&mut state),
    pbData,
    cbData
  );
  SymCryptSha3_256Result(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHA3_256_STATE>(&mut state),
    pbResult
  )
}

pub fn SymCryptSha3_256Append(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_256_STATE],
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

pub fn SymCryptSha3_256Init(pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_256_STATE])
{
  crate::sha3::SymCryptKeccakInit(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE>(
      &mut (pState[0usize]).ks
    ),
    136u32,
    6u8
  )
}

pub fn SymCryptSha3_256Result(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_256_STATE],
  pbResult: &mut [u8]
)
{
  crate::sha3::SymCryptKeccakExtract(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE>(
      &mut (pState[0usize]).ks
    ),
    pbResult,
    32usize,
    1u8
  )
}

pub fn SymCryptSha3_256StateCopy(
  pSrc: &[crate::symcrypt_internal::SYMCRYPT_SHA3_256_STATE],
  pDst: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_256_STATE]
)
{ pDst[0usize] = pSrc[0usize] }

pub const sha3_256KATAnswer: [u8; 32] =
    [58u8, 152u8, 93u8, 167u8, 79u8, 226u8, 37u8, 178u8, 4u8, 92u8, 23u8, 45u8, 107u8, 211u8, 144u8,
        189u8, 133u8, 95u8, 8u8, 110u8, 62u8, 157u8, 82u8, 91u8, 70u8, 191u8, 226u8, 69u8, 17u8,
        67u8, 21u8, 50u8];
