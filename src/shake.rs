#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub fn SymCryptShake128(pbData: &[u8], cbData: usize, pbResult: &mut [u8], cbResult: usize)
{
  let mut state: crate::symcrypt_internal::SYMCRYPT_SHAKE128_STATE = Default::default();
  SymCryptShake128Init(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHAKE128_STATE>(&mut state)
  );
  SymCryptShake128Append(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHAKE128_STATE>(&mut state),
    pbData,
    cbData
  );
  SymCryptShake128Extract(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHAKE128_STATE>(&mut state),
    pbResult,
    cbResult,
    1u8
  )
}

pub fn SymCryptShake128Append(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHAKE128_STATE],
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

pub fn SymCryptShake128Default(pbData: &[u8], cbData: usize, pbResult: &mut [u8])
{ SymCryptShake128(pbData, cbData, pbResult, 32usize) }

pub fn SymCryptShake128Extract(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHAKE128_STATE],
  pbResult: &mut [u8],
  cbResult: usize,
  bWipe: u8
)
{
  crate::sha3::SymCryptKeccakExtract(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE>(
      &mut (pState[0usize]).ks
    ),
    pbResult,
    cbResult,
    bWipe
  )
}

pub fn SymCryptShake128Init(pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHAKE128_STATE])
{
  crate::sha3::SymCryptKeccakInit(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE>(
      &mut (pState[0usize]).ks
    ),
    168u32,
    31u8
  )
}

pub fn SymCryptShake128Result(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHAKE128_STATE],
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

pub fn SymCryptShake128StateCopy(
  pSrc: &[crate::symcrypt_internal::SYMCRYPT_SHAKE128_STATE],
  pDst: &mut [crate::symcrypt_internal::SYMCRYPT_SHAKE128_STATE]
)
{ pDst[0usize] = pSrc[0usize] }

pub fn SymCryptShake256(pbData: &[u8], cbData: usize, pbResult: &mut [u8], cbResult: usize)
{
  let mut state: crate::symcrypt_internal::SYMCRYPT_SHAKE256_STATE = Default::default();
  SymCryptShake256Init(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHAKE256_STATE>(&mut state)
  );
  SymCryptShake256Append(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHAKE256_STATE>(&mut state),
    pbData,
    cbData
  );
  SymCryptShake256Extract(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHAKE256_STATE>(&mut state),
    pbResult,
    cbResult,
    1u8
  )
}

pub fn SymCryptShake256Append(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHAKE256_STATE],
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

pub fn SymCryptShake256Default(pbData: &[u8], cbData: usize, pbResult: &mut [u8])
{ SymCryptShake256(pbData, cbData, pbResult, 64usize) }

pub fn SymCryptShake256Extract(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHAKE256_STATE],
  pbResult: &mut [u8],
  cbResult: usize,
  bWipe: u8
)
{
  crate::sha3::SymCryptKeccakExtract(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE>(
      &mut (pState[0usize]).ks
    ),
    pbResult,
    cbResult,
    bWipe
  )
}

pub fn SymCryptShake256Init(pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHAKE256_STATE])
{
  crate::sha3::SymCryptKeccakInit(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE>(
      &mut (pState[0usize]).ks
    ),
    136u32,
    31u8
  )
}

pub fn SymCryptShake256Result(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHAKE256_STATE],
  pbResult: &mut [u8]
)
{
  crate::sha3::SymCryptKeccakExtract(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE>(
      &mut (pState[0usize]).ks
    ),
    pbResult,
    64usize,
    1u8
  )
}

pub fn SymCryptShake256StateCopy(
  pSrc: &[crate::symcrypt_internal::SYMCRYPT_SHAKE256_STATE],
  pDst: &mut [crate::symcrypt_internal::SYMCRYPT_SHAKE256_STATE]
)
{ pDst[0usize] = pSrc[0usize] }

pub const shake128KATAnswer: [u8; 32] =
    [88u8, 129u8, 9u8, 45u8, 216u8, 24u8, 191u8, 92u8, 248u8, 163u8, 221u8, 183u8, 147u8, 251u8,
        203u8, 167u8, 64u8, 151u8, 213u8, 197u8, 38u8, 166u8, 211u8, 95u8, 151u8, 184u8, 51u8, 81u8,
        148u8, 15u8, 44u8, 200u8];

pub const shake256KATAnswer: [u8; 64] =
    [72u8, 51u8, 102u8, 96u8, 19u8, 96u8, 168u8, 119u8, 28u8, 104u8, 99u8, 8u8, 12u8, 196u8, 17u8,
        77u8, 141u8, 180u8, 69u8, 48u8, 248u8, 241u8, 225u8, 238u8, 79u8, 148u8, 234u8, 55u8, 231u8,
        139u8, 87u8, 57u8, 213u8, 161u8, 91u8, 239u8, 24u8, 106u8, 83u8, 134u8, 199u8, 87u8, 68u8,
        192u8, 82u8, 126u8, 31u8, 170u8, 159u8, 135u8, 38u8, 228u8, 98u8, 161u8, 42u8, 79u8, 235u8,
        6u8, 189u8, 136u8, 1u8, 231u8, 81u8, 228u8];
