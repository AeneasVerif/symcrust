// The SYMCRYPT_ERROR C enum, mapped to Rust
//
// FIXME: for now, this is manually kept in sync between Rust and C -- can we automate?

#[derive(PartialEq, Debug)]
#[repr(C)]
pub enum Error {
    NoError = 0,
    Unused = 0x8000, // Start our error codes here so they're easier to distinguish
    WrongKeySize,
    WrongBlockSize,
    WrongDataSize,
    WrongNonceSize,
    WrongTagSize,
    WrongIterationCount,
    AuthenticationFailure,
    ExternalFailure,
    FipsFailure,
    HardwareFailure,
    NotImplemented,
    InvalidBlob,
    BufferTooSmall,
    InvalidArgument,
    MemoryAllocationFailure,
    SignatureVerificationFailure,
    IncompatibleFormat,
    ValueTooLarge,
    SessionReplayFailure,
    HbsNoOtsKeysLeft,
    HbsPublicRootMismatch,
}

// General-purpose functions that for now, remain implemented in C within SymCrypt.
//
// TODO: customize the build of this Rust crate to be either dynamic or static, and in the static
// case, bind SymCryptCallbackRandom instead. See commented-out sketch, below.

// #[cfg(not(feature = "dynamic"))]
// extern "C" {
//     fn SymCryptCallbackRandom(pbBuffer: *mut u8, cbBuffer: usize) -> MLKEM_ERROR;
// }

// #[cfg(feature = "dynamic")]
#[link(name = "symcrypt")]
extern "C" {
    fn SymCryptRandom(pbBuffer: *mut u8, cbBuffer: usize);
    fn SymCryptModuleInit(api: u32, minor: u32);
    fn SymCryptWipe(pb_data: *mut u8, cb_data: usize);
}

pub(crate) fn random(dst: &mut [u8]) -> Error {
    // #[cfg(not(feature = "dynamic"))]
    // unsafe {
    //     SymCryptCallbackRandom(dst.as_mut_ptr(), dst.len())
    // }
    // #[cfg(feature = "dynamic")]
    unsafe {
        SymCryptRandom(dst.as_mut_ptr(), dst.len());
        Error::NoError
    }
}

// TODO: manually kept in sync with C code -- can this be automated?
pub(crate) fn init() {
    unsafe {
        SymCryptModuleInit(103, 8);
    }
}

pub fn wipe(pb_data: *mut u8, cb_data: usize) {
    unsafe {
        SymCryptWipe(pb_data, cb_data);
    }
}

pub fn wipe_slice<T>(pb_dst: &mut [T]) {
    wipe(pb_dst.as_mut_ptr() as *mut u8, pb_dst.len() * size_of::<T>() );
}
