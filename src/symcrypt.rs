pub(crate)
fn SYMCRYPT_LOAD_LSBFIRST64 (x: &[u8]) -> u64 {
    u64::from_le_bytes(x[0..8].try_into().unwrap())
}

pub(crate)
fn SYMCRYPT_STORE_LSBFIRST64 (x: &mut [u8], v: u64) {
    x[0..8].copy_from_slice(&u64::to_le_bytes(v))
}
