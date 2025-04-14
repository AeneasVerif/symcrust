#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

pub const KeccakIotaK: [u64; 24] =
    [1u64, 32898u64, 9223372036854808714u64, 9223372039002292224u64, 32907u64, 2147483649u64,
        9223372039002292353u64, 9223372036854808585u64, 138u64, 136u64, 2147516425u64, 2147483658u64,
        2147516555u64, 9223372036854775947u64, 9223372036854808713u64, 9223372036854808579u64,
        9223372036854808578u64, 9223372036854775936u64, 32778u64, 9223372039002259466u64,
        9223372039002292353u64, 9223372036854808704u64, 2147483649u64, 9223372039002292232u64];

pub const KeccakRhoK: [u8; 25] =
    [0u8, 1u8, 62u8, 28u8, 27u8, 36u8, 44u8, 6u8, 55u8, 20u8, 3u8, 10u8, 43u8, 25u8, 39u8, 41u8,
        45u8, 15u8, 21u8, 8u8, 18u8, 2u8, 61u8, 56u8, 14u8];

pub fn SymCryptKeccakAppend(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE],
  mut pbData: &[u8],
  mut cbData: usize
)
{
  if (pState[0usize]).squeezeMode != 0u8 { SymCryptKeccakReset(pState) };
  while
  cbData > 0usize && (pState[0usize]).stateIndex & 7u32 != 0u32
  {
    SymCryptKeccakAppendByte(pState, pbData[0usize]);
    pbData = &pbData[1usize..];
    cbData = cbData.wrapping_sub(1usize)
  };
  if (pState[0usize]).stateIndex == (pState[0usize]).inputBlockSize
  {
    SymCryptKeccakPermute(&mut (pState[0usize]).state);
    (pState[0usize]).stateIndex = 0u32
  };
  let uFullLanes: usize = cbData.wrapping_div(8usize);
  if uFullLanes > 0usize
  {
    SymCryptKeccakAppendLanes(pState, pbData, uFullLanes);
    pbData = &pbData[uFullLanes.wrapping_mul(8usize)..];
    cbData = cbData.wrapping_sub(uFullLanes.wrapping_mul(8usize))
  };
  SymCryptKeccakAppendBytes(pState, pbData, cbData)
}

#[inline] pub fn SymCryptKeccakAppendByte(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE],
  val: u8
)
{
  (pState[0usize]).state[(pState[0usize]).stateIndex.wrapping_div(8u32) as usize] ^=
      (val as u64).wrapping_shl(8u32.wrapping_mul((pState[0usize]).stateIndex.wrapping_rem(8u32)));
  (pState[0usize]).stateIndex = (pState[0usize]).stateIndex.wrapping_add(1u32)
}

#[inline] pub fn SymCryptKeccakAppendBytes(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE],
  pbBuffer: &[u8],
  cbBuffer: usize
)
{
  for i in 0usize..cbBuffer
  {
    (pState[0usize]).state[(pState[0usize]).stateIndex.wrapping_add(i as u32).wrapping_div(8u32)
    as
    usize] ^=
        (pbBuffer[i] as u64).wrapping_shl(
          8u64.wrapping_mul(
            (pState[0usize]).stateIndex.wrapping_add(i as u32).wrapping_rem(8u32) as u64
          )
          as
          u32
        )
  };
  (pState[0usize]).stateIndex = (pState[0usize]).stateIndex.wrapping_add(cbBuffer as u32)
}

pub fn SymCryptKeccakAppendLanes(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE],
  pbData: &[u8],
  uLaneCount: usize
)
{
  let mut uLaneIndex: u32 = (pState[0usize]).stateIndex.wrapping_div(8u32);
  for i in 0usize..uLaneCount
  {
    (pState[0usize]).state[uLaneIndex as usize] ^=
        crate::symcrypt::SYMCRYPT_LOAD_LSBFIRST64(&pbData[i.wrapping_mul(8usize)..]);
    (pState[0usize]).stateIndex = (pState[0usize]).stateIndex.wrapping_add(8u32);
    uLaneIndex = uLaneIndex.wrapping_add(1u32);
    if (pState[0usize]).stateIndex == (pState[0usize]).inputBlockSize
    {
      SymCryptKeccakPermute(&mut (pState[0usize]).state);
      (pState[0usize]).stateIndex = 0u32;
      uLaneIndex = 0u32
    }
  }
}

pub fn SymCryptKeccakApplyPadding(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE]
)
{
  let uLanePos: u32 = (pState[0usize]).stateIndex.wrapping_div(8u32);
  let uBytePos: u32 = (pState[0usize]).stateIndex.wrapping_rem(8u32);
  (pState[0usize]).state[uLanePos as usize] ^=
      ((pState[0usize]).paddingValue as u64).wrapping_shl(8u32.wrapping_mul(uBytePos));
  (pState[0usize]).state[(pState[0usize]).inputBlockSize.wrapping_div(8u32).wrapping_sub(1u32)
  as
  usize] ^=
      1u64.wrapping_shl(63u32);
  SymCryptKeccakPermute(&mut (pState[0usize]).state);
  (pState[0usize]).stateIndex = 0u32;
  (pState[0usize]).squeezeMode = 1u8
}

pub fn SymCryptKeccakExtract(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE],
  mut pbResult: &mut [u8],
  mut cbResult: usize,
  bWipe: u8
)
{
  if (pState[0usize]).squeezeMode == 0u8 { SymCryptKeccakApplyPadding(pState) };
  if cbResult > 0usize && (pState[0usize]).stateIndex == (pState[0usize]).inputBlockSize
  {
    SymCryptKeccakPermute(&mut (pState[0usize]).state);
    (pState[0usize]).stateIndex = 0u32
  };
  while
  cbResult > 0usize && (pState[0usize]).stateIndex & 7u32 != 0u32
  {
    pbResult[0usize] = SymCryptKeccakExtractByte(pState);
    pbResult = &mut pbResult[1usize..];
    cbResult = cbResult.wrapping_sub(1usize)
  };
  let uFullLanes: usize = cbResult.wrapping_div(8usize);
  if uFullLanes > 0usize
  {
    SymCryptKeccakExtractLanes(pState, pbResult, uFullLanes);
    pbResult = &mut pbResult[uFullLanes.wrapping_mul(8usize)..];
    cbResult = cbResult.wrapping_sub(uFullLanes.wrapping_mul(8usize))
  };
  while
  cbResult > 0usize
  {
    if (pState[0usize]).stateIndex == (pState[0usize]).inputBlockSize
    {
      SymCryptKeccakPermute(&mut (pState[0usize]).state);
      (pState[0usize]).stateIndex = 0u32
    };
    pbResult[0usize] = SymCryptKeccakExtractByte(pState);
    pbResult = &mut pbResult[1usize..];
    cbResult = cbResult.wrapping_sub(1usize)
  };
  if bWipe != 0u8 { SymCryptKeccakReset(pState) }
}

#[inline] pub fn SymCryptKeccakExtractByte(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE]
) ->
    u8
{
  let ret: u8 =
      (((pState[0usize]).state[(pState[0usize]).stateIndex.wrapping_div(8u32) as usize]).wrapping_shr(
        8u32.wrapping_mul((pState[0usize]).stateIndex.wrapping_rem(8u32))
      )
      &
      255u64)
      as
      u8;
  (pState[0usize]).stateIndex = (pState[0usize]).stateIndex.wrapping_add(1u32);
  return ret
}

pub fn SymCryptKeccakExtractLanes(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE],
  pbResult: &mut [u8],
  uLaneCount: usize
)
{
  let mut uLaneIndex: u32 = (pState[0usize]).stateIndex.wrapping_div(8u32);
  for i in 0usize..uLaneCount
  {
    if (pState[0usize]).stateIndex == (pState[0usize]).inputBlockSize
    {
      SymCryptKeccakPermute(&mut (pState[0usize]).state);
      (pState[0usize]).stateIndex = 0u32;
      uLaneIndex = 0u32
    };
    crate::symcrypt::SYMCRYPT_STORE_LSBFIRST64(
      &mut pbResult[i.wrapping_mul(8usize)..],
      (pState[0usize]).state[uLaneIndex as usize]
    );
    (pState[0usize]).stateIndex = (pState[0usize]).stateIndex.wrapping_add(8u32);
    uLaneIndex = uLaneIndex.wrapping_add(1u32)
  }
}

pub fn SymCryptKeccakInit(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE],
  inputBlockSize: u32,
  paddingValue: u8
)
{
  (pState[0usize]).inputBlockSize = inputBlockSize;
  (pState[0usize]).paddingValue = paddingValue;
  SymCryptKeccakReset(pState)
}

pub fn SymCryptKeccakPermute(pState: &mut [u64])
{
  for r in 0i32..24i32
  {
    {
      let mut colSum: [u64; 5] = [0u64; 5usize];
      colSum[0usize] =
          pState[0i32.wrapping_add(0i32) as usize] ^ pState[5i32.wrapping_add(0i32) as usize]
          ^
          pState[10i32.wrapping_add(0i32) as usize]
          ^
          pState[15i32.wrapping_add(0i32) as usize]
          ^
          pState[20i32.wrapping_add(0i32) as usize];
      colSum[1usize] =
          pState[0i32.wrapping_add(1i32) as usize] ^ pState[5i32.wrapping_add(1i32) as usize]
          ^
          pState[10i32.wrapping_add(1i32) as usize]
          ^
          pState[15i32.wrapping_add(1i32) as usize]
          ^
          pState[20i32.wrapping_add(1i32) as usize];
      colSum[2usize] =
          pState[0i32.wrapping_add(2i32) as usize] ^ pState[5i32.wrapping_add(2i32) as usize]
          ^
          pState[10i32.wrapping_add(2i32) as usize]
          ^
          pState[15i32.wrapping_add(2i32) as usize]
          ^
          pState[20i32.wrapping_add(2i32) as usize];
      colSum[3usize] =
          pState[0i32.wrapping_add(3i32) as usize] ^ pState[5i32.wrapping_add(3i32) as usize]
          ^
          pState[10i32.wrapping_add(3i32) as usize]
          ^
          pState[15i32.wrapping_add(3i32) as usize]
          ^
          pState[20i32.wrapping_add(3i32) as usize];
      colSum[4usize] =
          pState[0i32.wrapping_add(4i32) as usize] ^ pState[5i32.wrapping_add(4i32) as usize]
          ^
          pState[10i32.wrapping_add(4i32) as usize]
          ^
          pState[15i32.wrapping_add(4i32) as usize]
          ^
          pState[20i32.wrapping_add(4i32) as usize];
      {
        let t: u64 =
            colSum[4usize]
            ^
            ((colSum[1usize]).wrapping_shl(1u32)
            |
            (colSum[1usize]).wrapping_shr(64i32.wrapping_sub(1i32) as u32))
            as
            u64;
        pState[0i32.wrapping_add(0i32) as usize] ^= t;
        pState[5i32.wrapping_add(0i32) as usize] ^= t;
        pState[10i32.wrapping_add(0i32) as usize] ^= t;
        pState[15i32.wrapping_add(0i32) as usize] ^= t;
        pState[20i32.wrapping_add(0i32) as usize] ^= t
      };
      {
        let t: u64 =
            colSum[0usize]
            ^
            ((colSum[2usize]).wrapping_shl(1u32)
            |
            (colSum[2usize]).wrapping_shr(64i32.wrapping_sub(1i32) as u32))
            as
            u64;
        pState[0i32.wrapping_add(1i32) as usize] ^= t;
        pState[5i32.wrapping_add(1i32) as usize] ^= t;
        pState[10i32.wrapping_add(1i32) as usize] ^= t;
        pState[15i32.wrapping_add(1i32) as usize] ^= t;
        pState[20i32.wrapping_add(1i32) as usize] ^= t
      };
      {
        let t: u64 =
            colSum[1usize]
            ^
            ((colSum[3usize]).wrapping_shl(1u32)
            |
            (colSum[3usize]).wrapping_shr(64i32.wrapping_sub(1i32) as u32))
            as
            u64;
        pState[0i32.wrapping_add(2i32) as usize] ^= t;
        pState[5i32.wrapping_add(2i32) as usize] ^= t;
        pState[10i32.wrapping_add(2i32) as usize] ^= t;
        pState[15i32.wrapping_add(2i32) as usize] ^= t;
        pState[20i32.wrapping_add(2i32) as usize] ^= t
      };
      {
        let t: u64 =
            colSum[2usize]
            ^
            ((colSum[4usize]).wrapping_shl(1u32)
            |
            (colSum[4usize]).wrapping_shr(64i32.wrapping_sub(1i32) as u32))
            as
            u64;
        pState[0i32.wrapping_add(3i32) as usize] ^= t;
        pState[5i32.wrapping_add(3i32) as usize] ^= t;
        pState[10i32.wrapping_add(3i32) as usize] ^= t;
        pState[15i32.wrapping_add(3i32) as usize] ^= t;
        pState[20i32.wrapping_add(3i32) as usize] ^= t
      };
      let t: u64 =
          colSum[3usize]
          ^
          ((colSum[0usize]).wrapping_shl(1u32)
          |
          (colSum[0usize]).wrapping_shr(64i32.wrapping_sub(1i32) as u32))
          as
          u64;
      pState[0i32.wrapping_add(4i32) as usize] ^= t;
      pState[5i32.wrapping_add(4i32) as usize] ^= t;
      pState[10i32.wrapping_add(4i32) as usize] ^= t;
      pState[15i32.wrapping_add(4i32) as usize] ^= t;
      pState[20i32.wrapping_add(4i32) as usize] ^= t
    };
    {
      {
        pState[1usize] =
            ((pState[1usize]).wrapping_shl(KeccakRhoK[1usize] as u32)
            |
            (pState[1usize]).wrapping_shr(64i32.wrapping_sub(KeccakRhoK[1usize] as i32) as u32))
            as
            u64;
        pState[2usize] =
            ((pState[2usize]).wrapping_shl(KeccakRhoK[2usize] as u32)
            |
            (pState[2usize]).wrapping_shr(64i32.wrapping_sub(KeccakRhoK[2usize] as i32) as u32))
            as
            u64;
        pState[3usize] =
            ((pState[3usize]).wrapping_shl(KeccakRhoK[3usize] as u32)
            |
            (pState[3usize]).wrapping_shr(64i32.wrapping_sub(KeccakRhoK[3usize] as i32) as u32))
            as
            u64;
        pState[4usize] =
            ((pState[4usize]).wrapping_shl(KeccakRhoK[4usize] as u32)
            |
            (pState[4usize]).wrapping_shr(64i32.wrapping_sub(KeccakRhoK[4usize] as i32) as u32))
            as
            u64
      };
      {
        pState[5i32.wrapping_mul(1i32).wrapping_add(0i32) as usize] =
            ((pState[5i32.wrapping_mul(1i32).wrapping_add(0i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(1i32).wrapping_add(0i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(1i32).wrapping_add(0i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(1i32).wrapping_add(0i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64;
        pState[5i32.wrapping_mul(1i32).wrapping_add(1i32) as usize] =
            ((pState[5i32.wrapping_mul(1i32).wrapping_add(1i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(1i32).wrapping_add(1i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(1i32).wrapping_add(1i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(1i32).wrapping_add(1i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64;
        pState[5i32.wrapping_mul(1i32).wrapping_add(2i32) as usize] =
            ((pState[5i32.wrapping_mul(1i32).wrapping_add(2i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(1i32).wrapping_add(2i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(1i32).wrapping_add(2i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(1i32).wrapping_add(2i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64;
        pState[5i32.wrapping_mul(1i32).wrapping_add(3i32) as usize] =
            ((pState[5i32.wrapping_mul(1i32).wrapping_add(3i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(1i32).wrapping_add(3i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(1i32).wrapping_add(3i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(1i32).wrapping_add(3i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64;
        pState[5i32.wrapping_mul(1i32).wrapping_add(4i32) as usize] =
            ((pState[5i32.wrapping_mul(1i32).wrapping_add(4i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(1i32).wrapping_add(4i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(1i32).wrapping_add(4i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(1i32).wrapping_add(4i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64
      };
      {
        pState[5i32.wrapping_mul(2i32).wrapping_add(0i32) as usize] =
            ((pState[5i32.wrapping_mul(2i32).wrapping_add(0i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(2i32).wrapping_add(0i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(2i32).wrapping_add(0i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(2i32).wrapping_add(0i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64;
        pState[5i32.wrapping_mul(2i32).wrapping_add(1i32) as usize] =
            ((pState[5i32.wrapping_mul(2i32).wrapping_add(1i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(2i32).wrapping_add(1i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(2i32).wrapping_add(1i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(2i32).wrapping_add(1i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64;
        pState[5i32.wrapping_mul(2i32).wrapping_add(2i32) as usize] =
            ((pState[5i32.wrapping_mul(2i32).wrapping_add(2i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(2i32).wrapping_add(2i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(2i32).wrapping_add(2i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(2i32).wrapping_add(2i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64;
        pState[5i32.wrapping_mul(2i32).wrapping_add(3i32) as usize] =
            ((pState[5i32.wrapping_mul(2i32).wrapping_add(3i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(2i32).wrapping_add(3i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(2i32).wrapping_add(3i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(2i32).wrapping_add(3i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64;
        pState[5i32.wrapping_mul(2i32).wrapping_add(4i32) as usize] =
            ((pState[5i32.wrapping_mul(2i32).wrapping_add(4i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(2i32).wrapping_add(4i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(2i32).wrapping_add(4i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(2i32).wrapping_add(4i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64
      };
      {
        pState[5i32.wrapping_mul(3i32).wrapping_add(0i32) as usize] =
            ((pState[5i32.wrapping_mul(3i32).wrapping_add(0i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(3i32).wrapping_add(0i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(3i32).wrapping_add(0i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(3i32).wrapping_add(0i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64;
        pState[5i32.wrapping_mul(3i32).wrapping_add(1i32) as usize] =
            ((pState[5i32.wrapping_mul(3i32).wrapping_add(1i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(3i32).wrapping_add(1i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(3i32).wrapping_add(1i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(3i32).wrapping_add(1i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64;
        pState[5i32.wrapping_mul(3i32).wrapping_add(2i32) as usize] =
            ((pState[5i32.wrapping_mul(3i32).wrapping_add(2i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(3i32).wrapping_add(2i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(3i32).wrapping_add(2i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(3i32).wrapping_add(2i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64;
        pState[5i32.wrapping_mul(3i32).wrapping_add(3i32) as usize] =
            ((pState[5i32.wrapping_mul(3i32).wrapping_add(3i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(3i32).wrapping_add(3i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(3i32).wrapping_add(3i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(3i32).wrapping_add(3i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64;
        pState[5i32.wrapping_mul(3i32).wrapping_add(4i32) as usize] =
            ((pState[5i32.wrapping_mul(3i32).wrapping_add(4i32) as usize]).wrapping_shl(
              KeccakRhoK[5i32.wrapping_mul(3i32).wrapping_add(4i32) as usize] as u32
            )
            |
            (pState[5i32.wrapping_mul(3i32).wrapping_add(4i32) as usize]).wrapping_shr(
              64i32.wrapping_sub(
                KeccakRhoK[5i32.wrapping_mul(3i32).wrapping_add(4i32) as usize] as i32
              )
              as
              u32
            ))
            as
            u64
      };
      pState[5i32.wrapping_mul(4i32).wrapping_add(0i32) as usize] =
          ((pState[5i32.wrapping_mul(4i32).wrapping_add(0i32) as usize]).wrapping_shl(
            KeccakRhoK[5i32.wrapping_mul(4i32).wrapping_add(0i32) as usize] as u32
          )
          |
          (pState[5i32.wrapping_mul(4i32).wrapping_add(0i32) as usize]).wrapping_shr(
            64i32.wrapping_sub(
              KeccakRhoK[5i32.wrapping_mul(4i32).wrapping_add(0i32) as usize] as i32
            )
            as
            u32
          ))
          as
          u64;
      pState[5i32.wrapping_mul(4i32).wrapping_add(1i32) as usize] =
          ((pState[5i32.wrapping_mul(4i32).wrapping_add(1i32) as usize]).wrapping_shl(
            KeccakRhoK[5i32.wrapping_mul(4i32).wrapping_add(1i32) as usize] as u32
          )
          |
          (pState[5i32.wrapping_mul(4i32).wrapping_add(1i32) as usize]).wrapping_shr(
            64i32.wrapping_sub(
              KeccakRhoK[5i32.wrapping_mul(4i32).wrapping_add(1i32) as usize] as i32
            )
            as
            u32
          ))
          as
          u64;
      pState[5i32.wrapping_mul(4i32).wrapping_add(2i32) as usize] =
          ((pState[5i32.wrapping_mul(4i32).wrapping_add(2i32) as usize]).wrapping_shl(
            KeccakRhoK[5i32.wrapping_mul(4i32).wrapping_add(2i32) as usize] as u32
          )
          |
          (pState[5i32.wrapping_mul(4i32).wrapping_add(2i32) as usize]).wrapping_shr(
            64i32.wrapping_sub(
              KeccakRhoK[5i32.wrapping_mul(4i32).wrapping_add(2i32) as usize] as i32
            )
            as
            u32
          ))
          as
          u64;
      pState[5i32.wrapping_mul(4i32).wrapping_add(3i32) as usize] =
          ((pState[5i32.wrapping_mul(4i32).wrapping_add(3i32) as usize]).wrapping_shl(
            KeccakRhoK[5i32.wrapping_mul(4i32).wrapping_add(3i32) as usize] as u32
          )
          |
          (pState[5i32.wrapping_mul(4i32).wrapping_add(3i32) as usize]).wrapping_shr(
            64i32.wrapping_sub(
              KeccakRhoK[5i32.wrapping_mul(4i32).wrapping_add(3i32) as usize] as i32
            )
            as
            u32
          ))
          as
          u64;
      pState[5i32.wrapping_mul(4i32).wrapping_add(4i32) as usize] =
          ((pState[5i32.wrapping_mul(4i32).wrapping_add(4i32) as usize]).wrapping_shl(
            KeccakRhoK[5i32.wrapping_mul(4i32).wrapping_add(4i32) as usize] as u32
          )
          |
          (pState[5i32.wrapping_mul(4i32).wrapping_add(4i32) as usize]).wrapping_shr(
            64i32.wrapping_sub(
              KeccakRhoK[5i32.wrapping_mul(4i32).wrapping_add(4i32) as usize] as i32
            )
            as
            u32
          ))
          as
          u64
    };
    {
      let t: u64 = pState[1usize];
      pState[1usize] = pState[6usize];
      pState[6usize] = pState[9usize];
      pState[9usize] = pState[22usize];
      pState[22usize] = pState[14usize];
      pState[14usize] = pState[20usize];
      pState[20usize] = pState[2usize];
      pState[2usize] = pState[12usize];
      pState[12usize] = pState[13usize];
      pState[13usize] = pState[19usize];
      pState[19usize] = pState[23usize];
      pState[23usize] = pState[15usize];
      pState[15usize] = pState[4usize];
      pState[4usize] = pState[24usize];
      pState[24usize] = pState[21usize];
      pState[21usize] = pState[8usize];
      pState[8usize] = pState[16usize];
      pState[16usize] = pState[5usize];
      pState[5usize] = pState[3usize];
      pState[3usize] = pState[18usize];
      pState[18usize] = pState[17usize];
      pState[17usize] = pState[11usize];
      pState[11usize] = pState[7usize];
      pState[7usize] = pState[10usize];
      pState[10usize] = t
    };
    {
      {
        let t1: u64 =
            pState[5i32.wrapping_mul(0i32).wrapping_add(0i32) as usize]
            ^
            ! pState[5i32.wrapping_mul(0i32).wrapping_add(1i32) as usize]
            &
            pState[5i32.wrapping_mul(0i32).wrapping_add(2i32) as usize];
        let t2: u64 =
            pState[5i32.wrapping_mul(0i32).wrapping_add(1i32) as usize]
            ^
            ! pState[5i32.wrapping_mul(0i32).wrapping_add(2i32) as usize]
            &
            pState[5i32.wrapping_mul(0i32).wrapping_add(3i32) as usize];
        pState[5i32.wrapping_mul(0i32).wrapping_add(2i32) as usize] ^=
            ! pState[5i32.wrapping_mul(0i32).wrapping_add(3i32) as usize]
            &
            pState[5i32.wrapping_mul(0i32).wrapping_add(4i32) as usize];
        pState[5i32.wrapping_mul(0i32).wrapping_add(3i32) as usize] ^=
            ! pState[5i32.wrapping_mul(0i32).wrapping_add(4i32) as usize]
            &
            pState[5i32.wrapping_mul(0i32).wrapping_add(0i32) as usize];
        pState[5i32.wrapping_mul(0i32).wrapping_add(4i32) as usize] ^=
            ! pState[5i32.wrapping_mul(0i32).wrapping_add(0i32) as usize]
            &
            pState[5i32.wrapping_mul(0i32).wrapping_add(1i32) as usize];
        pState[5i32.wrapping_mul(0i32).wrapping_add(0i32) as usize] = t1;
        pState[5i32.wrapping_mul(0i32).wrapping_add(1i32) as usize] = t2
      };
      {
        let t1: u64 =
            pState[5i32.wrapping_mul(1i32).wrapping_add(0i32) as usize]
            ^
            ! pState[5i32.wrapping_mul(1i32).wrapping_add(1i32) as usize]
            &
            pState[5i32.wrapping_mul(1i32).wrapping_add(2i32) as usize];
        let t2: u64 =
            pState[5i32.wrapping_mul(1i32).wrapping_add(1i32) as usize]
            ^
            ! pState[5i32.wrapping_mul(1i32).wrapping_add(2i32) as usize]
            &
            pState[5i32.wrapping_mul(1i32).wrapping_add(3i32) as usize];
        pState[5i32.wrapping_mul(1i32).wrapping_add(2i32) as usize] ^=
            ! pState[5i32.wrapping_mul(1i32).wrapping_add(3i32) as usize]
            &
            pState[5i32.wrapping_mul(1i32).wrapping_add(4i32) as usize];
        pState[5i32.wrapping_mul(1i32).wrapping_add(3i32) as usize] ^=
            ! pState[5i32.wrapping_mul(1i32).wrapping_add(4i32) as usize]
            &
            pState[5i32.wrapping_mul(1i32).wrapping_add(0i32) as usize];
        pState[5i32.wrapping_mul(1i32).wrapping_add(4i32) as usize] ^=
            ! pState[5i32.wrapping_mul(1i32).wrapping_add(0i32) as usize]
            &
            pState[5i32.wrapping_mul(1i32).wrapping_add(1i32) as usize];
        pState[5i32.wrapping_mul(1i32).wrapping_add(0i32) as usize] = t1;
        pState[5i32.wrapping_mul(1i32).wrapping_add(1i32) as usize] = t2
      };
      {
        let t1: u64 =
            pState[5i32.wrapping_mul(2i32).wrapping_add(0i32) as usize]
            ^
            ! pState[5i32.wrapping_mul(2i32).wrapping_add(1i32) as usize]
            &
            pState[5i32.wrapping_mul(2i32).wrapping_add(2i32) as usize];
        let t2: u64 =
            pState[5i32.wrapping_mul(2i32).wrapping_add(1i32) as usize]
            ^
            ! pState[5i32.wrapping_mul(2i32).wrapping_add(2i32) as usize]
            &
            pState[5i32.wrapping_mul(2i32).wrapping_add(3i32) as usize];
        pState[5i32.wrapping_mul(2i32).wrapping_add(2i32) as usize] ^=
            ! pState[5i32.wrapping_mul(2i32).wrapping_add(3i32) as usize]
            &
            pState[5i32.wrapping_mul(2i32).wrapping_add(4i32) as usize];
        pState[5i32.wrapping_mul(2i32).wrapping_add(3i32) as usize] ^=
            ! pState[5i32.wrapping_mul(2i32).wrapping_add(4i32) as usize]
            &
            pState[5i32.wrapping_mul(2i32).wrapping_add(0i32) as usize];
        pState[5i32.wrapping_mul(2i32).wrapping_add(4i32) as usize] ^=
            ! pState[5i32.wrapping_mul(2i32).wrapping_add(0i32) as usize]
            &
            pState[5i32.wrapping_mul(2i32).wrapping_add(1i32) as usize];
        pState[5i32.wrapping_mul(2i32).wrapping_add(0i32) as usize] = t1;
        pState[5i32.wrapping_mul(2i32).wrapping_add(1i32) as usize] = t2
      };
      {
        let t1: u64 =
            pState[5i32.wrapping_mul(3i32).wrapping_add(0i32) as usize]
            ^
            ! pState[5i32.wrapping_mul(3i32).wrapping_add(1i32) as usize]
            &
            pState[5i32.wrapping_mul(3i32).wrapping_add(2i32) as usize];
        let t2: u64 =
            pState[5i32.wrapping_mul(3i32).wrapping_add(1i32) as usize]
            ^
            ! pState[5i32.wrapping_mul(3i32).wrapping_add(2i32) as usize]
            &
            pState[5i32.wrapping_mul(3i32).wrapping_add(3i32) as usize];
        pState[5i32.wrapping_mul(3i32).wrapping_add(2i32) as usize] ^=
            ! pState[5i32.wrapping_mul(3i32).wrapping_add(3i32) as usize]
            &
            pState[5i32.wrapping_mul(3i32).wrapping_add(4i32) as usize];
        pState[5i32.wrapping_mul(3i32).wrapping_add(3i32) as usize] ^=
            ! pState[5i32.wrapping_mul(3i32).wrapping_add(4i32) as usize]
            &
            pState[5i32.wrapping_mul(3i32).wrapping_add(0i32) as usize];
        pState[5i32.wrapping_mul(3i32).wrapping_add(4i32) as usize] ^=
            ! pState[5i32.wrapping_mul(3i32).wrapping_add(0i32) as usize]
            &
            pState[5i32.wrapping_mul(3i32).wrapping_add(1i32) as usize];
        pState[5i32.wrapping_mul(3i32).wrapping_add(0i32) as usize] = t1;
        pState[5i32.wrapping_mul(3i32).wrapping_add(1i32) as usize] = t2
      };
      let t1: u64 =
          pState[5i32.wrapping_mul(4i32).wrapping_add(0i32) as usize]
          ^
          ! pState[5i32.wrapping_mul(4i32).wrapping_add(1i32) as usize]
          &
          pState[5i32.wrapping_mul(4i32).wrapping_add(2i32) as usize];
      let t2: u64 =
          pState[5i32.wrapping_mul(4i32).wrapping_add(1i32) as usize]
          ^
          ! pState[5i32.wrapping_mul(4i32).wrapping_add(2i32) as usize]
          &
          pState[5i32.wrapping_mul(4i32).wrapping_add(3i32) as usize];
      pState[5i32.wrapping_mul(4i32).wrapping_add(2i32) as usize] ^=
          ! pState[5i32.wrapping_mul(4i32).wrapping_add(3i32) as usize]
          &
          pState[5i32.wrapping_mul(4i32).wrapping_add(4i32) as usize];
      pState[5i32.wrapping_mul(4i32).wrapping_add(3i32) as usize] ^=
          ! pState[5i32.wrapping_mul(4i32).wrapping_add(4i32) as usize]
          &
          pState[5i32.wrapping_mul(4i32).wrapping_add(0i32) as usize];
      pState[5i32.wrapping_mul(4i32).wrapping_add(4i32) as usize] ^=
          ! pState[5i32.wrapping_mul(4i32).wrapping_add(0i32) as usize]
          &
          pState[5i32.wrapping_mul(4i32).wrapping_add(1i32) as usize];
      pState[5i32.wrapping_mul(4i32).wrapping_add(0i32) as usize] = t1;
      pState[5i32.wrapping_mul(4i32).wrapping_add(1i32) as usize] = t2
    };
    pState[0usize] ^= KeccakIotaK[r as usize]
  }
}

pub fn SymCryptKeccakReset(pState: &mut [crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE])
{
  for i in 0usize..25usize { (pState[0usize]).state[i] = 0u64 };
  (pState[0usize]).stateIndex = 0u32;
  (pState[0usize]).squeezeMode = 0u8
}

pub fn SymCryptKeccakZeroAppendBlock(
  pState: &mut [crate::symcrypt_internal::SYMCRYPT_KECCAK_STATE]
)
{
  SymCryptKeccakPermute(&mut (pState[0usize]).state);
  (pState[0usize]).stateIndex = 0u32
}
