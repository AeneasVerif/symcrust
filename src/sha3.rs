#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(unused_assignments)]
#![allow(unreachable_patterns)]

#[inline(always)]
pub
fn
KECCAK_CHI(state: &mut [u64])
{
  KECCAK_CHI_ROW(state, 0i32);
  KECCAK_CHI_ROW(state, 1i32);
  KECCAK_CHI_ROW(state, 2i32);
  KECCAK_CHI_ROW(state, 3i32);
  KECCAK_CHI_ROW(state, 4i32)
}

#[inline(always)]
pub
fn
KECCAK_CHI_ROW(state: &mut [u64], r: i32)
{
  let t1: u64 =
      state[5i32.wrapping_mul(r).wrapping_add(0i32) as usize]
      ^
      ! state[5i32.wrapping_mul(r).wrapping_add(1i32) as usize]
      &
      state[5i32.wrapping_mul(r).wrapping_add(2i32) as usize];
  let t2: u64 =
      state[5i32.wrapping_mul(r).wrapping_add(1i32) as usize]
      ^
      ! state[5i32.wrapping_mul(r).wrapping_add(2i32) as usize]
      &
      state[5i32.wrapping_mul(r).wrapping_add(3i32) as usize];
  state[5i32.wrapping_mul(r).wrapping_add(2i32) as usize] ^=
      ! state[5i32.wrapping_mul(r).wrapping_add(3i32) as usize]
      &
      state[5i32.wrapping_mul(r).wrapping_add(4i32) as usize];
  state[5i32.wrapping_mul(r).wrapping_add(3i32) as usize] ^=
      ! state[5i32.wrapping_mul(r).wrapping_add(4i32) as usize]
      &
      state[5i32.wrapping_mul(r).wrapping_add(0i32) as usize];
  state[5i32.wrapping_mul(r).wrapping_add(4i32) as usize] ^=
      ! state[5i32.wrapping_mul(r).wrapping_add(0i32) as usize]
      &
      state[5i32.wrapping_mul(r).wrapping_add(1i32) as usize];
  state[5i32.wrapping_mul(r).wrapping_add(0i32) as usize] = t1;
  state[5i32.wrapping_mul(r).wrapping_add(1i32) as usize] = t2
}

#[inline(always)]
pub
fn
KECCAK_COLUMN_SUM(state: &[u64], c: usize) ->
    u64
{
  return
  state[0u64.wrapping_add(c as u64) as usize] ^ state[5u64.wrapping_add(c as u64) as usize]
  ^
  state[10u64.wrapping_add(c as u64) as usize]
  ^
  state[15u64.wrapping_add(c as u64) as usize]
  ^
  state[20u64.wrapping_add(c as u64) as usize]
}

#[inline(always)]
pub
fn
KECCAK_COLUMN_UPDATE(state: &mut [u64], c: usize, w: u64)
{
  let t: u64 = w;
  state[0u64.wrapping_add(c as u64) as usize] ^= t;
  state[5u64.wrapping_add(c as u64) as usize] ^= t;
  state[10u64.wrapping_add(c as u64) as usize] ^= t;
  state[15u64.wrapping_add(c as u64) as usize] ^= t;
  state[20u64.wrapping_add(c as u64) as usize] ^= t
}

#[inline(always)]
pub
fn
KECCAK_IOTA(state: &mut [u64], rnd: i32)
{ state[0usize] ^= KeccakIotaK[rnd as usize] }

#[inline(always)]
pub
fn
KECCAK_PERM_ROUND(state: &mut [u64], rnd: i32)
{
  KECCAK_THETA(state);
  KECCAK_RHO(state);
  KECCAK_PI(state);
  KECCAK_CHI(state);
  KECCAK_IOTA(state, rnd)
}

#[inline(always)]
pub
fn
KECCAK_PI(state: &mut [u64])
{
  let t: u64 = state[1usize];
  state[1usize] = state[6usize];
  state[6usize] = state[9usize];
  state[9usize] = state[22usize];
  state[22usize] = state[14usize];
  state[14usize] = state[20usize];
  state[20usize] = state[2usize];
  state[2usize] = state[12usize];
  state[12usize] = state[13usize];
  state[13usize] = state[19usize];
  state[19usize] = state[23usize];
  state[23usize] = state[15usize];
  state[15usize] = state[4usize];
  state[4usize] = state[24usize];
  state[24usize] = state[21usize];
  state[21usize] = state[8usize];
  state[8usize] = state[16usize];
  state[16usize] = state[5usize];
  state[5usize] = state[3usize];
  state[3usize] = state[18usize];
  state[18usize] = state[17usize];
  state[17usize] = state[11usize];
  state[11usize] = state[7usize];
  state[7usize] = state[10usize];
  state[10usize] = t
}

#[inline(always)]
pub
fn
KECCAK_RHO(state: &mut [u64])
{
  KECCAK_RHO_ROW0(state);
  KECCAK_RHO_ROW(state, 1i32);
  KECCAK_RHO_ROW(state, 2i32);
  KECCAK_RHO_ROW(state, 3i32);
  KECCAK_RHO_ROW(state, 4i32)
}

#[inline(always)]
pub
fn
KECCAK_RHO_ROW(state: &mut [u64], r: i32)
{
  state[5i32.wrapping_mul(r).wrapping_add(0i32) as usize] =
      ((state[5i32.wrapping_mul(r).wrapping_add(0i32) as usize]).wrapping_shl(
        KeccakRhoK[5i32.wrapping_mul(r).wrapping_add(0i32) as usize] as u32
      )
      |
      (state[5i32.wrapping_mul(r).wrapping_add(0i32) as usize]).wrapping_shr(
        64i32.wrapping_sub(KeccakRhoK[5i32.wrapping_mul(r).wrapping_add(0i32) as usize] as i32)
        as
        u32
      ))
      as
      u64;
  state[5i32.wrapping_mul(r).wrapping_add(1i32) as usize] =
      ((state[5i32.wrapping_mul(r).wrapping_add(1i32) as usize]).wrapping_shl(
        KeccakRhoK[5i32.wrapping_mul(r).wrapping_add(1i32) as usize] as u32
      )
      |
      (state[5i32.wrapping_mul(r).wrapping_add(1i32) as usize]).wrapping_shr(
        64i32.wrapping_sub(KeccakRhoK[5i32.wrapping_mul(r).wrapping_add(1i32) as usize] as i32)
        as
        u32
      ))
      as
      u64;
  state[5i32.wrapping_mul(r).wrapping_add(2i32) as usize] =
      ((state[5i32.wrapping_mul(r).wrapping_add(2i32) as usize]).wrapping_shl(
        KeccakRhoK[5i32.wrapping_mul(r).wrapping_add(2i32) as usize] as u32
      )
      |
      (state[5i32.wrapping_mul(r).wrapping_add(2i32) as usize]).wrapping_shr(
        64i32.wrapping_sub(KeccakRhoK[5i32.wrapping_mul(r).wrapping_add(2i32) as usize] as i32)
        as
        u32
      ))
      as
      u64;
  state[5i32.wrapping_mul(r).wrapping_add(3i32) as usize] =
      ((state[5i32.wrapping_mul(r).wrapping_add(3i32) as usize]).wrapping_shl(
        KeccakRhoK[5i32.wrapping_mul(r).wrapping_add(3i32) as usize] as u32
      )
      |
      (state[5i32.wrapping_mul(r).wrapping_add(3i32) as usize]).wrapping_shr(
        64i32.wrapping_sub(KeccakRhoK[5i32.wrapping_mul(r).wrapping_add(3i32) as usize] as i32)
        as
        u32
      ))
      as
      u64;
  state[5i32.wrapping_mul(r).wrapping_add(4i32) as usize] =
      ((state[5i32.wrapping_mul(r).wrapping_add(4i32) as usize]).wrapping_shl(
        KeccakRhoK[5i32.wrapping_mul(r).wrapping_add(4i32) as usize] as u32
      )
      |
      (state[5i32.wrapping_mul(r).wrapping_add(4i32) as usize]).wrapping_shr(
        64i32.wrapping_sub(KeccakRhoK[5i32.wrapping_mul(r).wrapping_add(4i32) as usize] as i32)
        as
        u32
      ))
      as
      u64
}

#[inline(always)]
pub
fn
KECCAK_RHO_ROW0(state: &mut [u64])
{
  state[1usize] =
      ((state[1usize]).wrapping_shl(KeccakRhoK[1usize] as u32)
      |
      (state[1usize]).wrapping_shr(64i32.wrapping_sub(KeccakRhoK[1usize] as i32) as u32))
      as
      u64;
  state[2usize] =
      ((state[2usize]).wrapping_shl(KeccakRhoK[2usize] as u32)
      |
      (state[2usize]).wrapping_shr(64i32.wrapping_sub(KeccakRhoK[2usize] as i32) as u32))
      as
      u64;
  state[3usize] =
      ((state[3usize]).wrapping_shl(KeccakRhoK[3usize] as u32)
      |
      (state[3usize]).wrapping_shr(64i32.wrapping_sub(KeccakRhoK[3usize] as i32) as u32))
      as
      u64;
  state[4usize] =
      ((state[4usize]).wrapping_shl(KeccakRhoK[4usize] as u32)
      |
      (state[4usize]).wrapping_shr(64i32.wrapping_sub(KeccakRhoK[4usize] as i32) as u32))
      as
      u64
}

#[inline(always)]
pub
fn
KECCAK_THETA(state: &mut [u64])
{
  let mut colSum: [u64; 5] = [0u64; 5usize];
  colSum[0usize] = KECCAK_COLUMN_SUM(state, 0usize);
  colSum[1usize] = KECCAK_COLUMN_SUM(state, 1usize);
  colSum[2usize] = KECCAK_COLUMN_SUM(state, 2usize);
  colSum[3usize] = KECCAK_COLUMN_SUM(state, 3usize);
  colSum[4usize] = KECCAK_COLUMN_SUM(state, 4usize);
  KECCAK_COLUMN_UPDATE(
    state,
    0usize,
    colSum[4usize]
    ^
    ((colSum[1usize]).wrapping_shl(1u32)
    |
    (colSum[1usize]).wrapping_shr(64i32.wrapping_sub(1i32) as u32))
    as
    u64
  );
  KECCAK_COLUMN_UPDATE(
    state,
    1usize,
    colSum[0usize]
    ^
    ((colSum[2usize]).wrapping_shl(1u32)
    |
    (colSum[2usize]).wrapping_shr(64i32.wrapping_sub(1i32) as u32))
    as
    u64
  );
  KECCAK_COLUMN_UPDATE(
    state,
    2usize,
    colSum[1usize]
    ^
    ((colSum[3usize]).wrapping_shl(1u32)
    |
    (colSum[3usize]).wrapping_shr(64i32.wrapping_sub(1i32) as u32))
    as
    u64
  );
  KECCAK_COLUMN_UPDATE(
    state,
    3usize,
    colSum[2usize]
    ^
    ((colSum[4usize]).wrapping_shl(1u32)
    |
    (colSum[4usize]).wrapping_shr(64i32.wrapping_sub(1i32) as u32))
    as
    u64
  );
  KECCAK_COLUMN_UPDATE(
    state,
    4usize,
    colSum[3usize]
    ^
    ((colSum[0usize]).wrapping_shl(1u32)
    |
    (colSum[0usize]).wrapping_shr(64i32.wrapping_sub(1i32) as u32))
    as
    u64
  )
}

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
{ for r in 0i32..24i32 { KECCAK_PERM_ROUND(pState, r) } }

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
