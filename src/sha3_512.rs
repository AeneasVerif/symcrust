#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub fn SymCryptSha3_512(pbData: &[u8], cbData: usize, pbResult: &mut [u8])
{
  let mut state: crate::symcrypt_internal::SYMCRYPT_SHA3_512_STATE = Default::default();
  SymCryptSha3_512Init(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHA3_512_STATE>(&mut state)
  );
  SymCryptSha3_512Append(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHA3_512_STATE>(&mut state),
    pbData,
    cbData
  );
  SymCryptSha3_512Result(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_SHA3_512_STATE>(&mut state),
    pbResult
  )
}

pub fn SymCryptSha3_512Append(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_512_STATE],
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

pub fn SymCryptSha3_512Init(pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_512_STATE])
{
  crate::sha3::SymCryptKeccakInit(
    std::slice::from_mut::<crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE>(
      &mut (pState[0usize]).ks
    ),
    72u32,
    6u8
  )
}

pub fn SymCryptSha3_512Result(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_512_STATE],
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

pub fn SymCryptSha3_512StateCopy(
  pSrc: &[crate::symcrypt_internal::SYMCRYPT_SHA3_512_STATE],
  pDst: &mut [crate::symcrypt_internal::SYMCRYPT_SHA3_512_STATE]
)
{ pDst[0usize] = pSrc[0usize] }

pub const sha3_512KATAnswer: [u8; 64] =
    [183u8, 81u8, 133u8, 11u8, 26u8, 87u8, 22u8, 138u8, 86u8, 147u8, 205u8, 146u8, 75u8, 107u8, 9u8,
        110u8, 8u8, 246u8, 33u8, 130u8, 116u8, 68u8, 247u8, 13u8, 136u8, 79u8, 93u8, 2u8, 64u8,
        210u8, 113u8, 46u8, 16u8, 225u8, 22u8, 233u8, 25u8, 42u8, 243u8, 201u8, 26u8, 126u8, 197u8,
        118u8, 71u8, 227u8, 147u8, 64u8, 87u8, 52u8, 11u8, 76u8, 244u8, 8u8, 213u8, 165u8, 101u8,
        146u8, 248u8, 39u8, 78u8, 236u8, 83u8, 240u8];
