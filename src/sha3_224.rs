#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub fn SymCryptSha3_224(pbData: &[u8], cbData: usize, pbResult: &mut [u8])
{
  let mut state: crate::symcrypt_internal::SYMCRYPT_SHA3_224_STATE = Default::default();
  SymCryptSha3_224Init(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHA3_224_STATE>(&mut state)
  );
  SymCryptSha3_224Append(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHA3_224_STATE>(&mut state),
    pbData,
    cbData
  );
  SymCryptSha3_224Result(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHA3_224_STATE>(&mut state),
    pbResult
  )
}

pub fn SymCryptSha3_224Append(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_224_STATE],
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

pub fn SymCryptSha3_224Init(pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_224_STATE])
{
  crate::sha3::SymCryptKeccakInit(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE>(
      &mut (pState[0usize]).ks
    ),
    144u32,
    6u8
  )
}

pub fn SymCryptSha3_224Result(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_224_STATE],
  pbResult: &mut [u8]
)
{
  crate::sha3::SymCryptKeccakExtract(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE>(
      &mut (pState[0usize]).ks
    ),
    pbResult,
    28usize,
    1u8
  )
}

pub fn SymCryptSha3_224StateCopy(
  pSrc: &[crate::symcrypt_internal::SYMCRYPT_SHA3_224_STATE],
  pDst: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_224_STATE]
)
{ pDst[0usize] = pSrc[0usize] }

pub const sha3_224KATAnswer: [u8; 28] =
    [230u8, 66u8, 130u8, 76u8, 63u8, 140u8, 242u8, 74u8, 208u8, 146u8, 52u8, 238u8, 125u8, 60u8,
        118u8, 111u8, 201u8, 163u8, 165u8, 22u8, 141u8, 12u8, 148u8, 173u8, 115u8, 180u8, 111u8,
        223u8];
