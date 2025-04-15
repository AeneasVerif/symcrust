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

// Allows printing errors, which is a prerequisite for using ERROR as an argument to
// std::result::Result.
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

// Allows using errors within std::result::Result.
impl std::error::Error for Error {}

// Allows using the ? operator to early-return in functions that return MLKEM_ERROR, capturing the
// fact that NO_ERROR is the success case.
// Note: this requires
impl std::ops::FromResidual<Result<std::convert::Infallible, Error>> for Error {
    fn from_residual(r: Result<std::convert::Infallible, Error>) -> Error {
        match r {
            Result::Ok(_) => Error::NoError,
            Result::Err(e) => e,
        }
    }
}

// General-purpose functions that for now, remain implemented in C within SymCrypt.

#[cfg(not(feature = "rand"))]
extern "C" {
    fn SymCryptRandom(pbBuffer: *mut u8, cbBuffer: usize);
    fn SymCryptModuleInit(api: u32, minor: u32);
}

#[cfg(not(feature = "rand"))]
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
#[cfg(not(feature = "rand"))]
pub(crate) fn init() {
    unsafe {
        SymCryptModuleInit(103, 8);
    }
}

#[cfg(feature = "rand")]
use rand::prelude::*;

#[cfg(feature = "rand")]
pub(crate)
fn init() {}

#[cfg(feature = "rand")]
pub(crate)
fn random(dst: &mut[u8]) -> Error {
    rand::rng().fill(dst);
    Error::NoError
}
