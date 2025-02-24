//
// mlkem.c   ML-KEM related functionality
//
// Copyright (c) Microsoft Corporation. Licensed under the MIT license.
//

use zeroize::Zeroize;

use crate::common::*;
use crate::key::*;
use crate::ntt::*;

use crate::c_for;

const fn SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(_nRows: usize) -> usize {
    384 * _nRows
}

// d and z are each 32 bytes
const SIZEOF_FORMAT_PRIVATE_SEED: usize = 2 * 32;
// s and t are encoded uncompressed vectors
// public seed, H(encapsulation key) and z are each 32 bytes
pub(crate) const fn SIZEOF_FORMAT_DECAPSULATION_KEY(_nRows: usize) -> usize {
    2 * SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(_nRows) + 3 * 32
}
// t is encoded uncompressed vector
// public seed is 32 bytes
pub(crate) const fn SIZEOF_FORMAT_ENCAPSULATION_KEY(_nRows: usize) -> usize {
    SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(_nRows) + 32
}

const CIPHERTEXT_SIZE_MLKEM512: usize = 768;
const CIPHERTEXT_SIZE_MLKEM768: usize = 1088;
const CIPHERTEXT_SIZE_MLKEM1024: usize = 1568;

// MLKEM key formats
// ==================
//  -   The below formats apply **only to external formats**: When somebody is
//      importing a key (from test vectors, for example) or exporting a key.
//      The internal format of the keys is not visible to the caller.

pub fn SymCryptMlKemSizeofKeyFormatFromParams(
    params: Params,
    mlKemkeyFormat: crate::key::Format,
) -> usize {
    let internalParams = get_internal_params_from_params(params);

    match mlKemkeyFormat {
        crate::key::Format::PrivateSeed => SIZEOF_FORMAT_PRIVATE_SEED,
        crate::key::Format::DecapsulationKey => {
            SIZEOF_FORMAT_DECAPSULATION_KEY(internalParams.n_rows as usize)
        }
        crate::key::Format::EncapsulationKey => {
            SIZEOF_FORMAT_ENCAPSULATION_KEY(internalParams.n_rows as usize)
        }
    }
}

pub fn SymCryptMlKemSizeofCiphertextFromParams(params: Params) -> usize {
    let internalParams = get_internal_params_from_params(params);

    // u vector encoded with nBitsOfU * MLWE_POLYNOMIAL_COEFFICIENTS bits per polynomial
    let cbU = (internalParams.n_rows as usize)
        * (internalParams.n_bits_of_u as usize)
        * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);
    // v polynomial encoded with nBitsOfV * MLWE_POLYNOMIAL_COEFFICIENTS bits
    let cbV = (internalParams.n_bits_of_v as usize) * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);

    assert!(
        (internalParams.params != Params::MlKem512) || ((cbU + cbV) == CIPHERTEXT_SIZE_MLKEM512)
    );
    assert!(
        (internalParams.params != Params::MlKem768) || ((cbU + cbV) == CIPHERTEXT_SIZE_MLKEM768)
    );
    assert!(
        (internalParams.params != Params::MlKem1024) || ((cbU + cbV) == CIPHERTEXT_SIZE_MLKEM1024)
    );

    cbU + cbV
}

fn SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed(
    pkMlKemkey: &mut Key,
    pCompTemps: &mut INTERNAL_COMPUTATION_TEMPORARIES,
) {
    let mut coordinates = [0u8; 2];

    let pShakeStateBase = &mut pCompTemps.hashState0;
    let pShakeStateWork = &mut pCompTemps.hashState1;
    let nRows = pkMlKemkey.params.n_rows;

    crate::hash::shake128_init(pShakeStateBase);
    crate::hash::shake128_append(pShakeStateBase, &pkMlKemkey.public_seed);

    c_for!(let mut i = 0u8; i<nRows; i += 1; {
        coordinates[1] = i;
        c_for!(let mut j=0u8; j<nRows; j += 1; {
            coordinates[0] = j;
            crate::hash::shake128_state_copy( pShakeStateBase, pShakeStateWork );
            crate::hash::shake128_append( pShakeStateWork, &coordinates);

            let a_transpose = pkMlKemkey.atranspose_mut();
            SymCryptMlKemPolyElementSampleNTTFromShake128( pShakeStateWork, &mut a_transpose[(i*nRows+j) as usize] );
        });
    });

    // no need to wipe; everything computed here is always public
}

fn SymCryptMlKemkeyComputeEncapsulationKeyHash(
    pkMlKemkey: &mut Key,
    pCompTemps: &mut INTERNAL_COMPUTATION_TEMPORARIES,
) {
    let pState = &mut pCompTemps.hashState0;
    let cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(pkMlKemkey.params.n_rows as usize);
    crate::hash::sha3_256_init(pState);
    crate::hash::sha3_256_append(pState, &pkMlKemkey.encoded_t[0..cbEncodedVector]);
    crate::hash::sha3_256_append(pState, &pkMlKemkey.public_seed);
    crate::hash::sha3_256_result(pState, &mut pkMlKemkey.encaps_key_hash);
}

fn SymCryptMlKemkeyExpandFromPrivateSeed(
    pkMlKemkey: &mut Key,
    pCompTemps: &mut INTERNAL_COMPUTATION_TEMPORARIES,
) {
    let mut privateSeedHash = [0u8; crate::hash::SHA3_512_RESULT_SIZE];
    let mut CBDSampleBuffer = [0u8; 3 * 64 + 1];
    // PVECTOR pvTmp;
    // PPOLYELEMENT_ACCUMULATOR paTmp;
    // UINT32 i;
    let nRows = pkMlKemkey.params.n_rows;
    let nEta1 = pkMlKemkey.params.n_eta1;
    let cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(nRows as usize);
    // const SIZE_T cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(nRows);
    // const UINT32 cbPolyElement = pkMlKemkey->params.cbPolyElement;
    // const UINT32 cbVector = pkMlKemkey->params.cbVector;

    assert!(pkMlKemkey.has_private_seed);
    assert!((nEta1 == 2) || (nEta1 == 3));

    // Note(Rust): there's a whole lot of NULL-checking going on in C, which presumably does not
    // happen here -- the checks for NULL in the C code seem to be unreachable, because at the
    // leaves, SymCryptPolyElementCreate cannot return NULL...?

    // (rho || sigma) = G(d || k)
    // use CBDSampleBuffer to concatenate the private seed and encoding of nRows
    CBDSampleBuffer[0..pkMlKemkey.private_seed.len()].copy_from_slice(&pkMlKemkey.private_seed);
    CBDSampleBuffer[pkMlKemkey.private_seed.len() /* == 32 */] = nRows;
    crate::hash::sha3_512(
        &CBDSampleBuffer[0..pkMlKemkey.private_seed.len() + 1],
        &mut privateSeedHash,
    );

    // copy public seed
    let pkLen = pkMlKemkey.public_seed.len();
    pkMlKemkey
        .public_seed
        .copy_from_slice(&privateSeedHash[0..pkLen]);

    // generate A from public seed
    SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed(pkMlKemkey, pCompTemps);

    // Initialize pShakeStateBase with sigma
    crate::hash::shake256_init(&mut pCompTemps.hashState0);
    crate::hash::shake256_append(
        &mut pCompTemps.hashState0,
        &privateSeedHash[pkMlKemkey.public_seed.len()..pkMlKemkey.public_seed.len() + 32],
    );

    // Expand s in place
    c_for!(let mut i = 0; i < nRows; i += 1; {
        CBDSampleBuffer[0] = i;
        crate::hash::shake256_state_copy( &mut pCompTemps.hashState0, &mut pCompTemps.hashState1 );
        crate::hash::shake256_append( &mut pCompTemps.hashState1, &CBDSampleBuffer[0..1] );

        crate::hash::shake256_extract( &mut pCompTemps.hashState1, &mut CBDSampleBuffer[0..64usize*(nEta1 as usize)], false);

        SymCryptMlKemPolyElementSampleCBDFromBytes( &CBDSampleBuffer, nEta1 as u32, &mut pkMlKemkey.s_mut()[i as usize]);
    });
    // Expand e in t, ready for multiply-add
    c_for!(let mut i = 0; i < nRows; i += 1; {
        CBDSampleBuffer[0] = nRows+i;
        // Note (Rust): it is much better to borrow the hash states *here*, rather than declaring
        // them at the beginning of the function. With the former style, the borrow lives for the
        // duration of the function call and one can use pCompTemps still; with the latter style,
        // pCompTemps is invalidated for the duration of the entire function.
        crate::hash::shake256_state_copy( &mut pCompTemps.hashState0, &mut pCompTemps.hashState1 );
        crate::hash::shake256_append( &mut pCompTemps.hashState1, &CBDSampleBuffer[0..1] );

        crate::hash::shake256_extract( &mut pCompTemps.hashState1, &mut CBDSampleBuffer[0..64*(nEta1 as usize)], false );

        SymCryptMlKemPolyElementSampleCBDFromBytes( &CBDSampleBuffer, nEta1 as u32, &mut pkMlKemkey.t_mut()[i as usize]);
    });

    // Perform NTT on s and e
    SymCryptMlKemVectorNTT(pkMlKemkey.s_mut());
    SymCryptMlKemVectorNTT(pkMlKemkey.t_mut());

    // pvTmp = s .* R
    let pvTmp = &mut pCompTemps.abVectorBuffer0[0..nRows as usize];
    SymCryptMlKemVectorMulR(pkMlKemkey.s_mut(), pvTmp);

    // t = ((A o (s .* R)) ./ R) + e = A o s + e
    let (a, t, _s) = pkMlKemkey.ats_mut();
    let paTmp = &mut pCompTemps.abPolyElementAccumulatorBuffer;
    SymCryptMlKemMatrixVectorMontMulAndAdd(
        a,
        &pCompTemps.abVectorBuffer0[0..nRows as usize],
        t,
        paTmp,
        nRows,
    );

    // transpose A
    SymCryptMlKemMatrixTranspose(pkMlKemkey.atranspose_mut(), nRows);

    // precompute byte-encoding of public vector t
    let (t, encodedT) = pkMlKemkey.t_encoded_t_mut();
    SymCryptMlKemVectorCompressAndEncode(t, 12, &mut encodedT[0..cbEncodedVector]);

    // precompute hash of encapsulation key blob
    SymCryptMlKemkeyComputeEncapsulationKeyHash(pkMlKemkey, pCompTemps);

    // Cleanup!
    privateSeedHash.zeroize();
    CBDSampleBuffer.zeroize();
}

//=====================================================
// Flags for asymmetric key generation and import

// These flags are introduced primarily for FIPS purposes. For FIPS 140-3 rather than expose to the
// caller the specifics of what tests will be run with various algorithms, we are sanitizing flags
// provided on asymmetric key generation and import to enable the caller to indicate their intent,
// and for SymCrypt to perform the required testing.
// Below we define the flags that can be passed and when a caller should set them.
// The specifics of what tests will be run are likely to change over time, as FIPS requirements and
// our understanding of how best to implement them, change over time. Callers should not rely on
// specific behavior.

// Validation required by FIPS is enabled by default. This flag enables a caller to opt out of this
// validation.
const FLAG_KEY_NO_FIPS: u32 = 0x100;

// When opting out of FIPS, SymCrypt may still perform some sanity checks on key import
// In very performance sensitive situations where a caller strongly trusts the values it is passing
// to SymCrypt and does not care about FIPS (or can statically prove properties about the imported
// keys), a caller may specify FLAG_KEY_MINIMAL_VALIDATION in addition to
// FLAG_KEY_NO_FIPS to skip costly checks
const FLAG_KEY_MINIMAL_VALIDATION: u32 = 0x200;

// Callers must specify what algorithm(s) a given asymmetric key will be used for.
// This information will be tracked by SymCrypt, and attempting to use the key in an algorithm it
// was not generated or imported for will result in failure.
// If no algorithm is specified then the key generation or import function will fail.
const FLAG_DLKEY_DSA: u32 = 0x1000;
const FLAG_DLKEY_DH: u32 = 0x2000;

const FLAG_ECKEY_ECDSA: u32 = 0x1000;
const FLAG_ECKEY_ECDH: u32 = 0x2000;

const FLAG_RSAKEY_SIGN: u32 = 0x1000;
const FLAG_RSAKEY_ENCRYPT: u32 = 0x2000;

pub fn SymCryptMlKemkeySetValue(
    pbSrc: &[u8],
    mlKemkeyFormat: crate::key::Format,
    flags: u32,
    pkMlKemkey: &mut Key,
) -> Error {
    // ERROR scError = NO_ERROR;
    let mut pbCurr: usize = 0;
    // PINTERNAL_COMPUTATION_TEMPORARIES pCompTemps = NULL;
    let nRows = pkMlKemkey.params.n_rows;
    let cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(nRows as usize);

    // Ensure only allowed flags are specified
    let allowedFlags: u32 = FLAG_KEY_NO_FIPS | FLAG_KEY_MINIMAL_VALIDATION;

    if (flags & !allowedFlags) != 0 {
        return Error::InvalidArgument;
    }

    // Check that minimal validation flag only specified with no fips
    if ((flags & FLAG_KEY_NO_FIPS) == 0) && ((flags & FLAG_KEY_MINIMAL_VALIDATION) != 0) {
        return Error::InvalidArgument;
    }

    // Note (Rust): ruled out by typing
    // if( mlKemkeyFormat == crate::key::Format_NULL )
    // {
    //     return MLKEM_ERROR::INVALID_ARGUMENT;
    // }

    if (flags & FLAG_KEY_NO_FIPS) == 0 {
        // FIXME
        // Ensure ML-KEM algorithm selftest is run before first use of ML-KEM algorithms;
        // notably _before_ first full KeyGen
        // RUN_SELFTEST_ONCE(
        //     SymCryptMlKemSelftest,
        //     SELFTEST_ALGORITHM_MLKEM);
    }

    let pCompTemps = Box::try_new(INTERNAL_COMPUTATION_TEMPORARIES {
        abVectorBuffer0: [POLYELEMENT_ZERO; MATRIX_MAX_NROWS],
        abVectorBuffer1: [POLYELEMENT_ZERO; MATRIX_MAX_NROWS],
        abPolyElementBuffer0: POLYELEMENT_ZERO,
        abPolyElementBuffer1: POLYELEMENT_ZERO,
        abPolyElementAccumulatorBuffer: [0; MLWE_POLYNOMIAL_COEFFICIENTS],
        hashState0: crate::hash::UNINITIALIZED_HASH_STATE,
        hashState1: crate::hash::UNINITIALIZED_HASH_STATE,
    });

    let mut pCompTemps = match pCompTemps {
        Result::Err(_) => return Error::MemoryAllocationFailure,
        Result::Ok(pCompTemps) => pCompTemps,
    };

    match mlKemkeyFormat {
        crate::key::Format::PrivateSeed => {
            if pbSrc.len() != SIZEOF_FORMAT_PRIVATE_SEED {
                return Error::WrongKeySize;
            }

            pkMlKemkey.has_private_seed = true;
            let l = pkMlKemkey.private_seed.len();
            pkMlKemkey.private_seed.copy_from_slice(&pbSrc[0..l]);
            pbCurr += l;

            pkMlKemkey.has_private_key = true;
            let l = pkMlKemkey.private_random.len();
            pkMlKemkey
                .private_random
                .copy_from_slice(&pbSrc[pbCurr..pbCurr + l]);
            pbCurr += l;

            SymCryptMlKemkeyExpandFromPrivateSeed(pkMlKemkey, &mut pCompTemps);
        }

        crate::key::Format::DecapsulationKey => {
            if pbSrc.len() != SIZEOF_FORMAT_DECAPSULATION_KEY(nRows as usize) {
                return Error::WrongKeySize;
            }

            // decode s
            let scError = SymCryptMlKemVectorDecodeAndDecompress(
                &pbSrc[pbCurr..pbCurr + cbEncodedVector],
                12,
                pkMlKemkey.s_mut(),
            );
            if scError != Error::NoError {
                return scError;
            }
            pbCurr += cbEncodedVector;

            // copy t and decode t
            pkMlKemkey.encoded_t[0..cbEncodedVector]
                .copy_from_slice(&pbSrc[pbCurr..pbCurr + cbEncodedVector]);
            pbCurr += cbEncodedVector;
            let (t, encodedT) = pkMlKemkey.t_encoded_t_mut();
            let scError =
                SymCryptMlKemVectorDecodeAndDecompress(&encodedT[0..cbEncodedVector], 12, t);
            if scError != Error::NoError {
                return scError;
            }

            // copy public seed and expand public matrix
            let l = pkMlKemkey.public_seed.len();
            pkMlKemkey
                .public_seed
                .copy_from_slice(&pbSrc[pbCurr..pbCurr + l]);
            pbCurr += pkMlKemkey.public_seed.len();
            SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed(pkMlKemkey, &mut pCompTemps);

            // transpose A
            SymCryptMlKemMatrixTranspose(pkMlKemkey.atranspose_mut(), nRows);

            // copy hash of encapsulation key
            let l = pkMlKemkey.encaps_key_hash.len();
            pkMlKemkey
                .encaps_key_hash
                .copy_from_slice(&pbSrc[pbCurr..pbCurr + l]);
            pbCurr += pkMlKemkey.encaps_key_hash.len();

            // copy private random
            let l = pkMlKemkey.private_random.len();
            pkMlKemkey
                .private_random
                .copy_from_slice(&pbSrc[pbCurr..pbCurr + l]);
            pbCurr += pkMlKemkey.private_random.len();

            pkMlKemkey.has_private_seed = false;
            pkMlKemkey.has_private_key = true;
        }

        crate::key::Format::EncapsulationKey => {
            if pbSrc.len() != SIZEOF_FORMAT_ENCAPSULATION_KEY(nRows as usize) {
                return Error::WrongKeySize;
            }

            // copy t and decode t
            pkMlKemkey.encoded_t[0..cbEncodedVector]
                .copy_from_slice(&pbSrc[pbCurr..pbCurr + cbEncodedVector]);
            pbCurr += cbEncodedVector;
            let (t, encodedT) = pkMlKemkey.t_encoded_t_mut();
            let scError =
                SymCryptMlKemVectorDecodeAndDecompress(&encodedT[0..cbEncodedVector], 12, t);
            if scError != Error::NoError {
                return scError;
            }

            // copy public seed and expand public matrix
            let l = pkMlKemkey.public_seed.len();
            pkMlKemkey
                .public_seed
                .copy_from_slice(&pbSrc[pbCurr..pbCurr + l]);
            pbCurr += pkMlKemkey.public_seed.len();
            SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed(pkMlKemkey, &mut pCompTemps);

            // transpose A
            SymCryptMlKemMatrixTranspose(pkMlKemkey.atranspose_mut(), nRows);

            // precompute hash of encapsulation key blob
            SymCryptMlKemkeyComputeEncapsulationKeyHash(pkMlKemkey, &mut pCompTemps);

            pkMlKemkey.has_private_seed = false;
            pkMlKemkey.has_private_key = false;
        }
    };
    // Note (Rust): exhaustiveness
    // else
    // {
    //     scError = NOT_IMPLEMENTED;
    //     goto cleanup;
    // }

    assert!(pbCurr == pbSrc.len());

    Error::NoError
    // cleanup:
    //     if( pCompTemps != NULL )
    //     {
    //         SymCryptWipe( pCompTemps, sizeof(*pCompTemps) );
    //         SymCryptCallbackFree( pCompTemps );
    //     }

    //     return scError;
}

pub fn SymCryptMlKemkeyGetValue(
    pkMlKemkey: &Key,
    pbDst: &mut [u8],
    // SIZE_T                      cbDst,
    mlKemkeyFormat: crate::key::Format,
    _flags: u32,
) -> Error {
    // ERROR scError = NO_ERROR;
    let mut pbCurr: usize = 0;
    let nRows = pkMlKemkey.params.n_rows;
    let cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(nRows as usize);

    //     if( mlKemkeyFormat == crate::key::Format_NULL )
    //     {
    //         scError = INVALID_ARGUMENT;
    //         goto cleanup;
    //     }

    match mlKemkeyFormat {
        crate::key::Format::PrivateSeed => {
            if pbDst.len() != SIZEOF_FORMAT_PRIVATE_SEED {
                return Error::WrongKeySize;
            }

            if !pkMlKemkey.has_private_seed {
                return Error::IncompatibleFormat;
            }

            pbDst[pbCurr..pbCurr + pkMlKemkey.private_seed.len()]
                .copy_from_slice(&pkMlKemkey.private_seed);
            pbCurr += pkMlKemkey.private_seed.len();

            pbDst[pbCurr..pbCurr + pkMlKemkey.private_random.len()]
                .copy_from_slice(&pkMlKemkey.private_random);
            pbCurr += pkMlKemkey.private_random.len();
        }

        crate::key::Format::DecapsulationKey => {
            if pbDst.len() != SIZEOF_FORMAT_DECAPSULATION_KEY(nRows as usize) {
                return Error::InvalidArgument;
            }

            if !pkMlKemkey.has_private_key {
                return Error::InvalidArgument;
            }

            // We don't precompute byte-encoding of private key as exporting decapsulation key is not a critical path operation
            // All other fields are kept in memory
            SymCryptMlKemVectorCompressAndEncode(
                pkMlKemkey.s(),
                12,
                &mut pbDst[0..cbEncodedVector],
            );
            pbCurr += cbEncodedVector;

            pbDst[pbCurr..pbCurr + cbEncodedVector]
                .copy_from_slice(&pkMlKemkey.encoded_t[0..cbEncodedVector]);
            pbCurr += cbEncodedVector;

            pbDst[pbCurr..pbCurr + pkMlKemkey.public_seed.len()]
                .copy_from_slice(&pkMlKemkey.public_seed);
            pbCurr += pkMlKemkey.public_seed.len();

            pbDst[pbCurr..pbCurr + pkMlKemkey.encaps_key_hash.len()]
                .copy_from_slice(&pkMlKemkey.encaps_key_hash);
            pbCurr += pkMlKemkey.encaps_key_hash.len();

            pbDst[pbCurr..pbCurr + pkMlKemkey.private_random.len()]
                .copy_from_slice(&pkMlKemkey.private_random);
            pbCurr += pkMlKemkey.private_random.len();
        }

        crate::key::Format::EncapsulationKey => {
            if pbDst.len() != SIZEOF_FORMAT_ENCAPSULATION_KEY(nRows as usize) {
                return Error::InvalidArgument;
            }

            pbDst[pbCurr..pbCurr + cbEncodedVector]
                .copy_from_slice(&pkMlKemkey.encoded_t[0..cbEncodedVector]);
            pbCurr += cbEncodedVector;

            pbDst[pbCurr..pbCurr + pkMlKemkey.public_seed.len()]
                .copy_from_slice(&pkMlKemkey.public_seed);
            pbCurr += pkMlKemkey.public_seed.len();
        } // else
          // {
          //     scError = NOT_IMPLEMENTED;
          //     goto cleanup;
          // }
    };

    assert!(pbCurr == pbDst.len());

    // cleanup:
    //     return scError;
    Error::NoError
}

pub fn SymCryptMlKemkeyGenerate(pkMlKemkey: &mut Key, flags: u32) -> Error {
    // ERROR scError = NO_ERROR;
    let mut privateSeed = [0u8; SIZEOF_FORMAT_PRIVATE_SEED];

    // Ensure only allowed flags are specified
    let allowedFlags: u32 = FLAG_KEY_NO_FIPS;

    if (flags & !allowedFlags) != 0 {
        return Error::InvalidArgument;
    }

    let scError = random(&mut privateSeed);
    if scError != Error::NoError {
        return scError;
    }

    let scError = SymCryptMlKemkeySetValue(
        &privateSeed,
        crate::key::Format::PrivateSeed,
        flags,
        pkMlKemkey,
    );
    if scError != Error::NoError {
        return scError;
    }

    // SymCryptMlKemkeySetValue ensures the self-test is run before
    // first operational use of MlKem

    // Awaiting feedback from NIST for discussion from PQC forum and CMUF
    // before implementing costly PCT on ML-KEM key generation which is
    // not expected by FIPS 203

    // cleanup:
    //     SymCryptWipeKnownSize( privateSeed, sizeof(privateSeed) );

    Error::NoError
}

const SIZEOF_MAX_CIPHERTEXT: usize = 1568;
const SIZEOF_AGREED_SECRET: usize = 32;
const SIZEOF_ENCAPS_RANDOM: usize = 32;

fn SymCryptMlKemEncapsulateInternal(
    pkMlKemkey: &mut Key,
    pbAgreedSecret: &mut [u8],
    pbCiphertext: &mut [u8],
    pbRandom: &[u8; SIZEOF_ENCAPS_RANDOM],
    pCompTemps: &mut INTERNAL_COMPUTATION_TEMPORARIES,
) -> Error {
    let cbAgreedSecret = pbAgreedSecret.len();
    let cbCiphertext = pbCiphertext.len();
    let mut CBDSampleBuffer = [0u8; 3 * 64 + 1];
    // ERROR scError = NO_ERROR;
    // PVECTOR pvrInner;
    // PVECTOR pvTmp;
    // PPOLYELEMENT peTmp0, peTmp1;
    // PPOLYELEMENT_ACCUMULATOR paTmp;
    // PSHA3_512_STATE pHashState = &pCompTemps->hashState0.sha3_512State;
    // PSHAKE256_STATE pShakeBaseState = &pCompTemps->hashState0.shake256State;
    // PSHAKE256_STATE pShakeWorkState = &pCompTemps->hashState1.shake256State;
    // SIZE_T cbU, cbV;
    // UINT32 i;
    let nRows = pkMlKemkey.params.n_rows;
    let nBitsOfU = pkMlKemkey.params.n_bits_of_u;
    let nBitsOfV = pkMlKemkey.params.n_bits_of_v;
    let nEta1 = pkMlKemkey.params.n_eta1;
    let nEta2 = pkMlKemkey.params.n_eta2;
    // let cbPolyElement = pkMlKemkey->params.cbPolyElement;
    // let cbVector = pkMlKemkey->params.cbVector;

    // u vector encoded with nBitsOfU * MLWE_POLYNOMIAL_COEFFICIENTS bits per polynomial
    let cbU = (nRows as usize) * (nBitsOfU as usize) * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);
    // v polynomial encoded with nBitsOfV * MLWE_POLYNOMIAL_COEFFICIENTS bits
    let cbV = (nBitsOfV as usize) * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);

    if (cbAgreedSecret != SIZEOF_AGREED_SECRET) || (cbCiphertext != cbU + cbV) {
        return Error::InvalidArgument;
    }

    let pvrInner = &mut pCompTemps.abVectorBuffer0[0..nRows as usize];
    let pvTmp = &mut pCompTemps.abVectorBuffer1[0..nRows as usize];
    let peTmp0 = &mut pCompTemps.abPolyElementBuffer0;
    let peTmp1 = &mut pCompTemps.abPolyElementBuffer1;
    let paTmp = &mut pCompTemps.abPolyElementAccumulatorBuffer;

    // CBDSampleBuffer = (K || rOuter) = SHA3-512(pbRandom || encapsKeyHash)
    crate::hash::sha3_512_init(&mut pCompTemps.hashState0);
    crate::hash::sha3_512_append(&mut pCompTemps.hashState0, pbRandom);
    crate::hash::sha3_512_append(&mut pCompTemps.hashState0, &pkMlKemkey.encaps_key_hash);
    // Note (Rust): should we have a type that is less strict for the output of sha3_512_result?
    // Note (Rust): no assert!(SIZEOF_AGREED_SECRET < SHA3_512_RESULT_SIZE)?
    crate::hash::sha3_512_result(
        &mut pCompTemps.hashState0,
        (&mut CBDSampleBuffer[0..crate::hash::SHA3_512_RESULT_SIZE])
            .try_into()
            .unwrap(),
    );

    // Write K to pbAgreedSecret
    pbAgreedSecret[0..SIZEOF_AGREED_SECRET]
        .copy_from_slice(&CBDSampleBuffer[0..SIZEOF_AGREED_SECRET]);

    // Initialize pShakeStateBase with rOuter
    crate::hash::shake256_init(&mut pCompTemps.hashState0);
    crate::hash::shake256_append(
        &mut pCompTemps.hashState0,
        &CBDSampleBuffer[cbAgreedSecret..cbAgreedSecret + 32],
    );

    // Expand rInner vector
    c_for!(let mut i=0u8; i<nRows; i += 1;
    {
        CBDSampleBuffer[0] = i;
        crate::hash::shake256_state_copy( &mut pCompTemps.hashState0, &mut pCompTemps.hashState1 );
        crate::hash::shake256_append( &mut pCompTemps.hashState1, &CBDSampleBuffer[0..1] );

        crate::hash::shake256_extract( &mut pCompTemps.hashState1, &mut CBDSampleBuffer[0..64usize*(nEta1 as usize)], false );

        SymCryptMlKemPolyElementSampleCBDFromBytes( & CBDSampleBuffer, nEta1 as u32, &mut pvrInner[i as usize]);
    });

    // Perform NTT on rInner
    SymCryptMlKemVectorNTT(pvrInner);

    // Set pvTmp to 0
    // TODO: write a helper function -- any way to do this better?
    pvTmp.copy_from_slice(&vec![POLYELEMENT_ZERO; nRows as usize].into_boxed_slice());
    // SymCryptMlKemVectorSetZero( pvTmp );

    // pvTmp = (Atranspose o rInner) ./ R
    SymCryptMlKemMatrixVectorMontMulAndAdd(
        pkMlKemkey.atranspose_mut(),
        pvrInner,
        pvTmp,
        paTmp,
        nRows,
    );

    // pvTmp = INTT(Atranspose o rInner)
    SymCryptMlKemVectorINTTAndMulR(pvTmp);

    // Expand e1 and add it to pvTmp - do addition PolyElement-wise to reduce memory usage
    c_for!(let mut i=0; i<nRows; i += 1; {
        CBDSampleBuffer[0] = nRows+i;
        crate::hash::shake256_state_copy( &mut pCompTemps.hashState0, &mut pCompTemps.hashState1 );
        crate::hash::shake256_append( &mut pCompTemps.hashState1, &CBDSampleBuffer[0..1] );

        crate::hash::shake256_extract( &mut pCompTemps.hashState1, &mut CBDSampleBuffer[0..64*(nEta2 as usize)], false );

        SymCryptMlKemPolyElementSampleCBDFromBytes( &CBDSampleBuffer, nEta2 as u32, peTmp0 );

        // Note (Rust): in-place operation here, was:
        // SymCryptMlKemPolyElementAdd( INTERNAL_MLKEM_VECTOR_ELEMENT(i, pvTmp), peTmp0, INTERNAL_MLKEM_VECTOR_ELEMENT(i, pvTmp) );
        // Added a copy -- TODO: measure performance impact of the copy
        let copy = pvTmp[i as usize];
        SymCryptMlKemPolyElementAdd( &copy, peTmp0, &mut pvTmp[i as usize] );

    });

    // pvTmp = u = INTT(Atranspose o rInner) + e1
    // Compress and encode u into prefix of ciphertext
    SymCryptMlKemVectorCompressAndEncode(pvTmp, nBitsOfU as u32, &mut pbCiphertext[0..cbU]);

    // peTmp0 = (t o r) ./ R
    SymCryptMlKemVectorMontDotProduct(pkMlKemkey.t_mut(), pvrInner, peTmp0, paTmp);

    // peTmp0 = INTT(t o r)
    SymCryptMlKemPolyElementINTTAndMulR(peTmp0);

    // Expand e2 polynomial in peTmp1
    CBDSampleBuffer[0] = 2 * nRows;
    crate::hash::shake256_state_copy(&mut pCompTemps.hashState0, &mut pCompTemps.hashState1);
    crate::hash::shake256_append(&mut pCompTemps.hashState1, &CBDSampleBuffer[0..1]);

    crate::hash::shake256_extract(
        &mut pCompTemps.hashState1,
        &mut CBDSampleBuffer[0..64 * (nEta2 as usize)],
        false,
    );

    SymCryptMlKemPolyElementSampleCBDFromBytes(&mut CBDSampleBuffer, nEta2 as u32, peTmp1);

    // peTmp = INTT(t o r) + e2
    // Note (Rust): in-place operation, was:
    // SymCryptMlKemPolyElementAdd( peTmp0, peTmp1, peTmp0 );
    // FIXME (measure performance issues, adjust)
    let copy = *peTmp0;
    SymCryptMlKemPolyElementAdd(&copy, peTmp1, peTmp0);

    // peTmp1 = mu
    SymCryptMlKemPolyElementDecodeAndDecompress(pbRandom, 1, peTmp1);

    // peTmp0 = v = INTT(t o r) + e2 + mu
    let copy = *peTmp0;
    // FIXME (same as above)
    SymCryptMlKemPolyElementAdd(&copy, peTmp1, peTmp0);

    // Compress and encode v into remainder of ciphertext
    SymCryptMlKemPolyElementCompressAndEncode(peTmp0, nBitsOfV as u32, &mut pbCiphertext[cbU..]);

    // cleanup:
    //     SymCryptWipeKnownSize( CBDSampleBuffer, sizeof(CBDSampleBuffer) );

    Error::NoError
}

pub fn SymCryptMlKemEncapsulateEx(
    pkMlKemkey: &mut Key,
    pbRandom: &[u8], // Note(Rust): we could statically require the right length, and have the FFI
    // wrapper enforce it
    pbAgreedSecret: &mut [u8],
    pbCiphertext: &mut [u8],
) -> Error {
    let cbRandom = pbRandom.len();
    // let cbAgreedSecret = pbAgreedSecret.len();
    // let cbCiphertext = pbCiphertext.len();

    if cbRandom != SIZEOF_ENCAPS_RANDOM {
        return Error::InvalidArgument;
    }

    let pCompTemps = Box::try_new(INTERNAL_COMPUTATION_TEMPORARIES {
        abVectorBuffer0: [POLYELEMENT_ZERO; MATRIX_MAX_NROWS],
        abVectorBuffer1: [POLYELEMENT_ZERO; MATRIX_MAX_NROWS],
        abPolyElementBuffer0: POLYELEMENT_ZERO,
        abPolyElementBuffer1: POLYELEMENT_ZERO,
        abPolyElementAccumulatorBuffer: [0; MLWE_POLYNOMIAL_COEFFICIENTS],
        hashState0: crate::hash::UNINITIALIZED_HASH_STATE,
        hashState1: crate::hash::UNINITIALIZED_HASH_STATE,
    });

    let mut pCompTemps = match pCompTemps {
        Result::Err(_) => return Error::MemoryAllocationFailure,
        Result::Ok(pCompTemps) => pCompTemps,
    };

    SymCryptMlKemEncapsulateInternal(
        pkMlKemkey,
        pbAgreedSecret,
        pbCiphertext,
        pbRandom.try_into().unwrap(),
        &mut pCompTemps,
    )
}

pub fn SymCryptMlKemEncapsulate(
    pkMlKemkey: &mut Key,
    pbAgreedSecret: &mut [u8],
    pbCiphertext: &mut [u8],
) -> Error {
    let mut pbm = [0u8; SIZEOF_ENCAPS_RANDOM];

    let scError = random(&mut pbm);
    if scError != Error::NoError {
        return scError;
    }

    SymCryptMlKemEncapsulateEx(pkMlKemkey, &pbm, pbAgreedSecret, pbCiphertext)
}

// cleanup:
//     SymCryptWipeKnownSize( pbm, sizeof(pbm) );

//     return scError;
// }

pub fn SymCryptMlKemDecapsulate(
    pkMlKemkey: &mut Key,
    pbCiphertext: &[u8],
    pbAgreedSecret: &mut [u8],
) -> Error {
    let cbCiphertext = pbCiphertext.len();
    let cbAgreedSecret = pbAgreedSecret.len();

    let pCompTemps = Box::try_new(INTERNAL_COMPUTATION_TEMPORARIES {
        abVectorBuffer0: [POLYELEMENT_ZERO; MATRIX_MAX_NROWS],
        abVectorBuffer1: [POLYELEMENT_ZERO; MATRIX_MAX_NROWS],
        abPolyElementBuffer0: POLYELEMENT_ZERO,
        abPolyElementBuffer1: POLYELEMENT_ZERO,
        abPolyElementAccumulatorBuffer: [0; MLWE_POLYNOMIAL_COEFFICIENTS],
        hashState0: crate::hash::UNINITIALIZED_HASH_STATE,
        hashState1: crate::hash::UNINITIALIZED_HASH_STATE,
    });

    let mut pCompTemps = match pCompTemps {
        Result::Err(_) => return Error::MemoryAllocationFailure,
        Result::Ok(pCompTemps) => pCompTemps,
    };

    let mut pbDecryptedRandom = [0u8; SIZEOF_ENCAPS_RANDOM];
    let mut pbDecapsulatedSecret = [0u8; SIZEOF_AGREED_SECRET];
    let mut pbImplicitRejectionSecret = [0u8; SIZEOF_AGREED_SECRET];
    // PBYTE pbReadCiphertext, pbReencapsulatedCiphertext;
    // BOOLEAN successfulReencrypt;

    // Note (Rust): we originally perform a single call to malloc() and use the first few bytes for
    // the temporary computations, then for the two temporary ciphertexts. Rust does not allow to
    // do this, so we perform two allocations.
    // Note (Rust): rather than use the (simple) solution below, which does not allow catching
    // memory allocation failures, we instead use the experimental try_with_capacity API:
    // let pbCompCiphers = vec![0u8; 2*cbCiphertext].into_boxed_slice();
    let pbCompCiphers = Vec::try_with_capacity(2 * cbCiphertext);
    let mut pbCompCiphers = match pbCompCiphers {
        Result::Ok(pbCompCiphers) => pbCompCiphers,
        Result::Err(_) => return Error::MemoryAllocationFailure,
    };
    pbCompCiphers.resize(2 * cbCiphertext, 0u8);
    let mut pbCompCiphers = pbCompCiphers.into_boxed_slice();
    let (pbReadCiphertext, pbReencapsulatedCiphertext) = pbCompCiphers.split_at_mut(cbCiphertext);

    //     ERROR scError = NO_ERROR;
    //     SIZE_T cbU, cbV, cbCopy;
    //     PVECTOR pvu;
    //     PPOLYELEMENT peTmp0, peTmp1;
    //     PPOLYELEMENT_ACCUMULATOR paTmp;
    //     PSHAKE256_STATE pShakeState;
    let nRows = pkMlKemkey.params.n_rows;
    let nBitsOfU = pkMlKemkey.params.n_bits_of_u;
    let nBitsOfV = pkMlKemkey.params.n_bits_of_v;
    // let cbPolyElement = pkMlKemkey.params.cbPolyElement;
    // let cbVector = pkMlKemkey.params.cbVector;

    // u vector encoded with nBitsOfU * MLWE_POLYNOMIAL_COEFFICIENTS bits per polynomial
    let cbU = nRows as usize * nBitsOfU as usize * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);
    // v polynomial encoded with nBitsOfV * MLWE_POLYNOMIAL_COEFFICIENTS bits
    let cbV = nBitsOfV as usize * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);

    if (cbAgreedSecret != SIZEOF_AGREED_SECRET)
        || (cbCiphertext != cbU + cbV)
        || !pkMlKemkey.has_private_key
    {
        return Error::InvalidArgument;
    }

    // Read the input ciphertext once to local pbReadCiphertext to ensure our view of ciphertext consistent
    pbReadCiphertext.copy_from_slice(pbCiphertext);

    let pvu = &mut pCompTemps.abVectorBuffer0[0..nRows as usize];
    let peTmp0 = &mut pCompTemps.abPolyElementBuffer0;
    let peTmp1 = &mut pCompTemps.abPolyElementBuffer1;
    let paTmp = &mut pCompTemps.abPolyElementAccumulatorBuffer;

    // Decode and decompress u
    let scError =
        SymCryptMlKemVectorDecodeAndDecompress(&mut pbReadCiphertext[0..cbU], nBitsOfU as u32, pvu);
    assert!(scError == Error::NoError);

    // Perform NTT on u
    SymCryptMlKemVectorNTT(pvu);

    // peTmp0 = (s o NTT(u)) ./ R
    SymCryptMlKemVectorMontDotProduct(pkMlKemkey.s_mut(), pvu, peTmp0, paTmp);

    // peTmp0 = INTT(s o NTT(u))
    SymCryptMlKemPolyElementINTTAndMulR(peTmp0);

    // Decode and decompress v
    let scError = SymCryptMlKemPolyElementDecodeAndDecompress(
        &mut pbReadCiphertext[cbU..],
        nBitsOfV as u32,
        peTmp1,
    );
    assert!(scError == Error::NoError);

    // peTmp0 = w = v - INTT(s o NTT(u))
    // FIXME
    let copy = *peTmp0;
    SymCryptMlKemPolyElementSub(peTmp1, &copy, peTmp0);

    // pbDecryptedRandom = m' = Encoding of w
    SymCryptMlKemPolyElementCompressAndEncode(peTmp0, 1, &mut pbDecryptedRandom);

    // Compute:
    //  pbDecapsulatedSecret = K' = Decapsulated secret (without implicit rejection)
    //  pbReencapsulatedCiphertext = c' = Ciphertext from re-encapsulating decrypted random value
    let scError = SymCryptMlKemEncapsulateInternal(
        pkMlKemkey,
        &mut pbDecapsulatedSecret,
        pbReencapsulatedCiphertext,
        &mut pbDecryptedRandom,
        &mut pCompTemps,
    );
    assert!(scError == Error::NoError);

    // Compute the secret we will return if using implicit rejection
    // pbImplicitRejectionSecret = K_bar = SHAKE256( z || c )
    let pShakeState = &mut pCompTemps.hashState0;
    crate::hash::shake256_init(pShakeState);
    crate::hash::shake256_append(pShakeState, &pkMlKemkey.private_random);
    crate::hash::shake256_append(pShakeState, pbReadCiphertext);
    crate::hash::shake256_extract(pShakeState, &mut pbImplicitRejectionSecret, false);

    // Constant time test if re-encryption successful
    let successfulReencrypt = pbReencapsulatedCiphertext == pbReadCiphertext;

    // If not successful, perform side-channel-safe copy of Implicit Rejection secret over Decapsulated secret
    let cbCopy = ((successfulReencrypt as usize).wrapping_sub(1)) & SIZEOF_AGREED_SECRET;
    pbDecapsulatedSecret[0..cbCopy].copy_from_slice(&pbImplicitRejectionSecret[0..cbCopy]);
    // FIXME, was:
    // SymCryptScsCopy( pbImplicitRejectionSecret, cbCopy, pbDecapsulatedSecret, SIZEOF_AGREED_SECRET );

    // Write agreed secret (with implicit rejection) to pbAgreedSecret
    pbAgreedSecret.copy_from_slice(&pbDecapsulatedSecret);

    // cleanup:
    //     if( pbAlloc != NULL )
    //     {
    //         SymCryptWipe( pbAlloc, cbAlloc );
    //         SymCryptCallbackFree( pbAlloc );
    //     }

    //     SymCryptWipeKnownSize( pbDecryptedRandom, sizeof(pbDecryptedRandom) );
    //     SymCryptWipeKnownSize( pbDecapsulatedSecret, sizeof(pbDecapsulatedSecret) );
    //     SymCryptWipeKnownSize( pbImplicitRejectionSecret, sizeof(pbImplicitRejectionSecret) );

    Error::NoError
}
