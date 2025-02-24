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

const fn SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(_n_rows: usize) -> usize {
    384 * _n_rows
}

// d and z are each 32 bytes
const SIZEOF_FORMAT_PRIVATE_SEED: usize = 2 * 32;
// s and t are encoded uncompressed vectors
// public seed, H(encapsulation key) and z are each 32 bytes
pub(crate) const fn SIZEOF_FORMAT_DECAPSULATION_KEY(_n_rows: usize) -> usize {
    2 * SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(_n_rows) + 3 * 32
}
// t is encoded uncompressed vector
// public seed is 32 bytes
pub(crate) const fn SIZEOF_FORMAT_ENCAPSULATION_KEY(_n_rows: usize) -> usize {
    SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(_n_rows) + 32
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
    let cb_u = (internalParams.n_rows as usize)
        * (internalParams.n_bits_of_u as usize)
        * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);
    // v polynomial encoded with nBitsOfV * MLWE_POLYNOMIAL_COEFFICIENTS bits
    let cb_v = (internalParams.n_bits_of_v as usize) * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);

    assert!(
        (internalParams.params != Params::MlKem512) || ((cb_u + cb_v) == CIPHERTEXT_SIZE_MLKEM512)
    );
    assert!(
        (internalParams.params != Params::MlKem768) || ((cb_u + cb_v) == CIPHERTEXT_SIZE_MLKEM768)
    );
    assert!(
        (internalParams.params != Params::MlKem1024) || ((cb_u + cb_v) == CIPHERTEXT_SIZE_MLKEM1024)
    );

    cb_u + cb_v
}

fn SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed(
    pk_mlkem_key: &mut Key,
    p_comp_temps: &mut INTERNAL_COMPUTATION_TEMPORARIES,
) {
    let mut coordinates = [0u8; 2];

    let p_shake_stateBase = &mut p_comp_temps.hashState0;
    let p_shake_stateWork = &mut p_comp_temps.hashState1;
    let n_rows = pk_mlkem_key.params.n_rows;

    crate::hash::shake128_init(p_shake_stateBase);
    crate::hash::shake128_append(p_shake_stateBase, &pk_mlkem_key.public_seed);

    c_for!(let mut i = 0u8; i<n_rows; i += 1; {
        coordinates[1] = i;
        c_for!(let mut j=0u8; j<n_rows; j += 1; {
            coordinates[0] = j;
            crate::hash::shake128_state_copy( p_shake_stateBase, p_shake_stateWork );
            crate::hash::shake128_append( p_shake_stateWork, &coordinates);

            let a_transpose = pk_mlkem_key.atranspose_mut();
            SymCryptMlKemPolyElementSampleNTTFromShake128( p_shake_stateWork, &mut a_transpose[(i*n_rows+j) as usize] );
        });
    });

    // no need to wipe; everything computed here is always public
}

fn SymCryptMlKemkeyComputeEncapsulationKeyHash(
    pk_mlkem_key: &mut Key,
    p_comp_temps: &mut INTERNAL_COMPUTATION_TEMPORARIES,
) {
    let p_state = &mut p_comp_temps.hashState0;
    let cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(pk_mlkem_key.params.n_rows as usize);
    crate::hash::sha3_256_init(p_state);
    crate::hash::sha3_256_append(p_state, &pk_mlkem_key.encoded_t[0..cbEncodedVector]);
    crate::hash::sha3_256_append(p_state, &pk_mlkem_key.public_seed);
    crate::hash::sha3_256_result(p_state, &mut pk_mlkem_key.encaps_key_hash);
}

fn SymCryptMlKemkeyExpandFromPrivateSeed(
    pk_mlkem_key: &mut Key,
    p_comp_temps: &mut INTERNAL_COMPUTATION_TEMPORARIES,
) {
    let mut private_seedHash = [0u8; crate::hash::SHA3_512_RESULT_SIZE];
    let mut CBDSampleBuffer = [0u8; 3 * 64 + 1];
    // PVECTOR pv_tmp;
    // PPOLYELEMENT_ACCUMULATOR pa_tmp;
    // UINT32 i;
    let n_rows = pk_mlkem_key.params.n_rows;
    let n_eta1 = pk_mlkem_key.params.n_eta1;
    let cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(n_rows as usize);
    // const SIZE_T cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(n_rows);
    // const UINT32 cbPolyElement = pk_mlkem_key->params.cbPolyElement;
    // const UINT32 cb_vector = pk_mlkem_key->params.cb_vector;

    assert!(pk_mlkem_key.has_private_seed);
    assert!((n_eta1 == 2) || (n_eta1 == 3));

    // Note(Rust): there's a whole lot of NULL-checking going on in C, which presumably does not
    // happen here -- the checks for NULL in the C code seem to be unreachable, because at the
    // leaves, SymCryptPolyElementCreate cannot return NULL...?

    // (rho || sigma) = G(d || k)
    // use CBDSampleBuffer to concatenate the private seed and encoding of n_rows
    CBDSampleBuffer[0..pk_mlkem_key.private_seed.len()].copy_from_slice(&pk_mlkem_key.private_seed);
    CBDSampleBuffer[pk_mlkem_key.private_seed.len() /* == 32 */] = n_rows;
    crate::hash::sha3_512(
        &CBDSampleBuffer[0..pk_mlkem_key.private_seed.len() + 1],
        &mut private_seedHash,
    );

    // copy public seed
    let pkLen = pk_mlkem_key.public_seed.len();
    pk_mlkem_key
        .public_seed
        .copy_from_slice(&private_seedHash[0..pkLen]);

    // generate A from public seed
    SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed(pk_mlkem_key, p_comp_temps);

    // Initialize p_shake_stateBase with sigma
    crate::hash::shake256_init(&mut p_comp_temps.hashState0);
    crate::hash::shake256_append(
        &mut p_comp_temps.hashState0,
        &private_seedHash[pk_mlkem_key.public_seed.len()..pk_mlkem_key.public_seed.len() + 32],
    );

    // Expand s in place
    c_for!(let mut i = 0; i < n_rows; i += 1; {
        CBDSampleBuffer[0] = i;
        crate::hash::shake256_state_copy( &mut p_comp_temps.hashState0, &mut p_comp_temps.hashState1 );
        crate::hash::shake256_append( &mut p_comp_temps.hashState1, &CBDSampleBuffer[0..1] );

        crate::hash::shake256_extract( &mut p_comp_temps.hashState1, &mut CBDSampleBuffer[0..64usize*(n_eta1 as usize)], false);

        SymCryptMlKemPolyElementSampleCBDFromBytes( &CBDSampleBuffer, n_eta1 as u32, &mut pk_mlkem_key.s_mut()[i as usize]);
    });
    // Expand e in t, ready for multiply-add
    c_for!(let mut i = 0; i < n_rows; i += 1; {
        CBDSampleBuffer[0] = n_rows+i;
        // Note (Rust): it is much better to borrow the hash states *here*, rather than declaring
        // them at the beginning of the function. With the former style, the borrow lives for the
        // duration of the function call and one can use p_comp_temps still; with the latter style,
        // p_comp_temps is invalidated for the duration of the entire function.
        crate::hash::shake256_state_copy( &mut p_comp_temps.hashState0, &mut p_comp_temps.hashState1 );
        crate::hash::shake256_append( &mut p_comp_temps.hashState1, &CBDSampleBuffer[0..1] );

        crate::hash::shake256_extract( &mut p_comp_temps.hashState1, &mut CBDSampleBuffer[0..64*(n_eta1 as usize)], false );

        SymCryptMlKemPolyElementSampleCBDFromBytes( &CBDSampleBuffer, n_eta1 as u32, &mut pk_mlkem_key.t_mut()[i as usize]);
    });

    // Perform NTT on s and e
    SymCryptMlKemVectorNTT(pk_mlkem_key.s_mut());
    SymCryptMlKemVectorNTT(pk_mlkem_key.t_mut());

    // pv_tmp = s .* R
    let pv_tmp = &mut p_comp_temps.abVectorBuffer0[0..n_rows as usize];
    SymCryptMlKemVectorMulR(pk_mlkem_key.s_mut(), pv_tmp);

    // t = ((A o (s .* R)) ./ R) + e = A o s + e
    let (a, t, _s) = pk_mlkem_key.ats_mut();
    let pa_tmp = &mut p_comp_temps.abPolyElementAccumulatorBuffer;
    SymCryptMlKemMatrixVectorMontMulAndAdd(
        a,
        &p_comp_temps.abVectorBuffer0[0..n_rows as usize],
        t,
        pa_tmp,
        n_rows,
    );

    // transpose A
    SymCryptMlKemMatrixTranspose(pk_mlkem_key.atranspose_mut(), n_rows);

    // precompute byte-encoding of public vector t
    let (t, encodedT) = pk_mlkem_key.t_encoded_t_mut();
    SymCryptMlKemVectorCompressAndEncode(t, 12, &mut encodedT[0..cbEncodedVector]);

    // precompute hash of encapsulation key blob
    SymCryptMlKemkeyComputeEncapsulationKeyHash(pk_mlkem_key, p_comp_temps);

    // Cleanup!
    private_seedHash.zeroize();
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
    pb_src: &[u8],
    mlKemkeyFormat: crate::key::Format,
    flags: u32,
    pk_mlkem_key: &mut Key,
) -> Error {
    // ERROR sc_error = NO_ERROR;
    let mut pb_curr: usize = 0;
    // PINTERNAL_COMPUTATION_TEMPORARIES p_comp_temps = NULL;
    let n_rows = pk_mlkem_key.params.n_rows;
    let cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(n_rows as usize);

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

    let p_comp_temps = Box::try_new(INTERNAL_COMPUTATION_TEMPORARIES {
        abVectorBuffer0: [POLYELEMENT_ZERO; MATRIX_MAX_NROWS],
        abVectorBuffer1: [POLYELEMENT_ZERO; MATRIX_MAX_NROWS],
        abPolyElementBuffer0: POLYELEMENT_ZERO,
        abPolyElementBuffer1: POLYELEMENT_ZERO,
        abPolyElementAccumulatorBuffer: [0; MLWE_POLYNOMIAL_COEFFICIENTS],
        hashState0: crate::hash::UNINITIALIZED_HASH_STATE,
        hashState1: crate::hash::UNINITIALIZED_HASH_STATE,
    });

    let mut p_comp_temps = match p_comp_temps {
        Result::Err(_) => return Error::MemoryAllocationFailure,
        Result::Ok(p_comp_temps) => p_comp_temps,
    };

    match mlKemkeyFormat {
        crate::key::Format::PrivateSeed => {
            if pb_src.len() != SIZEOF_FORMAT_PRIVATE_SEED {
                return Error::WrongKeySize;
            }

            pk_mlkem_key.has_private_seed = true;
            let l = pk_mlkem_key.private_seed.len();
            pk_mlkem_key.private_seed.copy_from_slice(&pb_src[0..l]);
            pb_curr += l;

            pk_mlkem_key.has_private_key = true;
            let l = pk_mlkem_key.private_random.len();
            pk_mlkem_key
                .private_random
                .copy_from_slice(&pb_src[pb_curr..pb_curr + l]);
            pb_curr += l;

            SymCryptMlKemkeyExpandFromPrivateSeed(pk_mlkem_key, &mut p_comp_temps);
        }

        crate::key::Format::DecapsulationKey => {
            if pb_src.len() != SIZEOF_FORMAT_DECAPSULATION_KEY(n_rows as usize) {
                return Error::WrongKeySize;
            }

            // decode s
            let sc_error = SymCryptMlKemVectorDecodeAndDecompress(
                &pb_src[pb_curr..pb_curr + cbEncodedVector],
                12,
                pk_mlkem_key.s_mut(),
            );
            if sc_error != Error::NoError {
                return sc_error;
            }
            pb_curr += cbEncodedVector;

            // copy t and decode t
            pk_mlkem_key.encoded_t[0..cbEncodedVector]
                .copy_from_slice(&pb_src[pb_curr..pb_curr + cbEncodedVector]);
            pb_curr += cbEncodedVector;
            let (t, encodedT) = pk_mlkem_key.t_encoded_t_mut();
            let sc_error =
                SymCryptMlKemVectorDecodeAndDecompress(&encodedT[0..cbEncodedVector], 12, t);
            if sc_error != Error::NoError {
                return sc_error;
            }

            // copy public seed and expand public matrix
            let l = pk_mlkem_key.public_seed.len();
            pk_mlkem_key
                .public_seed
                .copy_from_slice(&pb_src[pb_curr..pb_curr + l]);
            pb_curr += pk_mlkem_key.public_seed.len();
            SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed(pk_mlkem_key, &mut p_comp_temps);

            // transpose A
            SymCryptMlKemMatrixTranspose(pk_mlkem_key.atranspose_mut(), n_rows);

            // copy hash of encapsulation key
            let l = pk_mlkem_key.encaps_key_hash.len();
            pk_mlkem_key
                .encaps_key_hash
                .copy_from_slice(&pb_src[pb_curr..pb_curr + l]);
            pb_curr += pk_mlkem_key.encaps_key_hash.len();

            // copy private random
            let l = pk_mlkem_key.private_random.len();
            pk_mlkem_key
                .private_random
                .copy_from_slice(&pb_src[pb_curr..pb_curr + l]);
            pb_curr += pk_mlkem_key.private_random.len();

            pk_mlkem_key.has_private_seed = false;
            pk_mlkem_key.has_private_key = true;
        }

        crate::key::Format::EncapsulationKey => {
            if pb_src.len() != SIZEOF_FORMAT_ENCAPSULATION_KEY(n_rows as usize) {
                return Error::WrongKeySize;
            }

            // copy t and decode t
            pk_mlkem_key.encoded_t[0..cbEncodedVector]
                .copy_from_slice(&pb_src[pb_curr..pb_curr + cbEncodedVector]);
            pb_curr += cbEncodedVector;
            let (t, encodedT) = pk_mlkem_key.t_encoded_t_mut();
            let sc_error =
                SymCryptMlKemVectorDecodeAndDecompress(&encodedT[0..cbEncodedVector], 12, t);
            if sc_error != Error::NoError {
                return sc_error;
            }

            // copy public seed and expand public matrix
            let l = pk_mlkem_key.public_seed.len();
            pk_mlkem_key
                .public_seed
                .copy_from_slice(&pb_src[pb_curr..pb_curr + l]);
            pb_curr += pk_mlkem_key.public_seed.len();
            SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed(pk_mlkem_key, &mut p_comp_temps);

            // transpose A
            SymCryptMlKemMatrixTranspose(pk_mlkem_key.atranspose_mut(), n_rows);

            // precompute hash of encapsulation key blob
            SymCryptMlKemkeyComputeEncapsulationKeyHash(pk_mlkem_key, &mut p_comp_temps);

            pk_mlkem_key.has_private_seed = false;
            pk_mlkem_key.has_private_key = false;
        }
    };
    // Note (Rust): exhaustiveness
    // else
    // {
    //     sc_error = NOT_IMPLEMENTED;
    //     goto cleanup;
    // }

    assert!(pb_curr == pb_src.len());

    Error::NoError
    // cleanup:
    //     if( p_comp_temps != NULL )
    //     {
    //         SymCryptWipe( p_comp_temps, sizeof(*p_comp_temps) );
    //         SymCryptCallbackFree( p_comp_temps );
    //     }

    //     return sc_error;
}

pub fn SymCryptMlKemkeyGetValue(
    pk_mlkem_key: &Key,
    pb_dst: &mut [u8],
    // SIZE_T                      cb_dst,
    mlKemkeyFormat: crate::key::Format,
    _flags: u32,
) -> Error {
    // ERROR sc_error = NO_ERROR;
    let mut pb_curr: usize = 0;
    let n_rows = pk_mlkem_key.params.n_rows;
    let cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(n_rows as usize);

    //     if( mlKemkeyFormat == crate::key::Format_NULL )
    //     {
    //         sc_error = INVALID_ARGUMENT;
    //         goto cleanup;
    //     }

    match mlKemkeyFormat {
        crate::key::Format::PrivateSeed => {
            if pb_dst.len() != SIZEOF_FORMAT_PRIVATE_SEED {
                return Error::WrongKeySize;
            }

            if !pk_mlkem_key.has_private_seed {
                return Error::IncompatibleFormat;
            }

            pb_dst[pb_curr..pb_curr + pk_mlkem_key.private_seed.len()]
                .copy_from_slice(&pk_mlkem_key.private_seed);
            pb_curr += pk_mlkem_key.private_seed.len();

            pb_dst[pb_curr..pb_curr + pk_mlkem_key.private_random.len()]
                .copy_from_slice(&pk_mlkem_key.private_random);
            pb_curr += pk_mlkem_key.private_random.len();
        }

        crate::key::Format::DecapsulationKey => {
            if pb_dst.len() != SIZEOF_FORMAT_DECAPSULATION_KEY(n_rows as usize) {
                return Error::InvalidArgument;
            }

            if !pk_mlkem_key.has_private_key {
                return Error::InvalidArgument;
            }

            // We don't precompute byte-encoding of private key as exporting decapsulation key is not a critical path operation
            // All other fields are kept in memory
            SymCryptMlKemVectorCompressAndEncode(
                pk_mlkem_key.s(),
                12,
                &mut pb_dst[0..cbEncodedVector],
            );
            pb_curr += cbEncodedVector;

            pb_dst[pb_curr..pb_curr + cbEncodedVector]
                .copy_from_slice(&pk_mlkem_key.encoded_t[0..cbEncodedVector]);
            pb_curr += cbEncodedVector;

            pb_dst[pb_curr..pb_curr + pk_mlkem_key.public_seed.len()]
                .copy_from_slice(&pk_mlkem_key.public_seed);
            pb_curr += pk_mlkem_key.public_seed.len();

            pb_dst[pb_curr..pb_curr + pk_mlkem_key.encaps_key_hash.len()]
                .copy_from_slice(&pk_mlkem_key.encaps_key_hash);
            pb_curr += pk_mlkem_key.encaps_key_hash.len();

            pb_dst[pb_curr..pb_curr + pk_mlkem_key.private_random.len()]
                .copy_from_slice(&pk_mlkem_key.private_random);
            pb_curr += pk_mlkem_key.private_random.len();
        }

        crate::key::Format::EncapsulationKey => {
            if pb_dst.len() != SIZEOF_FORMAT_ENCAPSULATION_KEY(n_rows as usize) {
                return Error::InvalidArgument;
            }

            pb_dst[pb_curr..pb_curr + cbEncodedVector]
                .copy_from_slice(&pk_mlkem_key.encoded_t[0..cbEncodedVector]);
            pb_curr += cbEncodedVector;

            pb_dst[pb_curr..pb_curr + pk_mlkem_key.public_seed.len()]
                .copy_from_slice(&pk_mlkem_key.public_seed);
            pb_curr += pk_mlkem_key.public_seed.len();
        } // else
          // {
          //     sc_error = NOT_IMPLEMENTED;
          //     goto cleanup;
          // }
    };

    assert!(pb_curr == pb_dst.len());

    // cleanup:
    //     return sc_error;
    Error::NoError
}

pub fn SymCryptMlKemkeyGenerate(pk_mlkem_key: &mut Key, flags: u32) -> Error {
    // ERROR sc_error = NO_ERROR;
    let mut private_seed = [0u8; SIZEOF_FORMAT_PRIVATE_SEED];

    // Ensure only allowed flags are specified
    let allowedFlags: u32 = FLAG_KEY_NO_FIPS;

    if (flags & !allowedFlags) != 0 {
        return Error::InvalidArgument;
    }

    let sc_error = random(&mut private_seed);
    if sc_error != Error::NoError {
        return sc_error;
    }

    let sc_error = SymCryptMlKemkeySetValue(
        &private_seed,
        crate::key::Format::PrivateSeed,
        flags,
        pk_mlkem_key,
    );
    if sc_error != Error::NoError {
        return sc_error;
    }

    // SymCryptMlKemkeySetValue ensures the self-test is run before
    // first operational use of MlKem

    // Awaiting feedback from NIST for discussion from PQC forum and CMUF
    // before implementing costly PCT on ML-KEM key generation which is
    // not expected by FIPS 203

    // cleanup:
    //     SymCryptWipeKnownSize( private_seed, sizeof(private_seed) );

    Error::NoError
}

const SIZEOF_MAX_CIPHERTEXT: usize = 1568;
const SIZEOF_AGREED_SECRET: usize = 32;
const SIZEOF_ENCAPS_RANDOM: usize = 32;

fn SymCryptMlKemEncapsulateInternal(
    pk_mlkem_key: &mut Key,
    pb_agreed_secret: &mut [u8],
    pb_ciphertext: &mut [u8],
    pb_random: &[u8; SIZEOF_ENCAPS_RANDOM],
    p_comp_temps: &mut INTERNAL_COMPUTATION_TEMPORARIES,
) -> Error {
    let cb_agreed_secret = pb_agreed_secret.len();
    let cb_ciphertext = pb_ciphertext.len();
    let mut CBDSampleBuffer = [0u8; 3 * 64 + 1];
    // ERROR sc_error = NO_ERROR;
    // PVECTOR pvrInner;
    // PVECTOR pv_tmp;
    // PPOLYELEMENT pe_tmp0, pe_tmp1;
    // PPOLYELEMENT_ACCUMULATOR pa_tmp;
    // PSHA3_512_STATE pHashState = &p_comp_temps->hashState0.sha3_512State;
    // PSHAKE256_STATE pShakeBaseState = &p_comp_temps->hashState0.shake256State;
    // PSHAKE256_STATE pShakeWorkState = &p_comp_temps->hashState1.shake256State;
    // SIZE_T cb_u, cb_v;
    // UINT32 i;
    let n_rows = pk_mlkem_key.params.n_rows;
    let nBitsOfU = pk_mlkem_key.params.n_bits_of_u;
    let nBitsOfV = pk_mlkem_key.params.n_bits_of_v;
    let n_eta1 = pk_mlkem_key.params.n_eta1;
    let n_eta2 = pk_mlkem_key.params.n_eta2;
    // let cbPolyElement = pk_mlkem_key->params.cbPolyElement;
    // let cb_vector = pk_mlkem_key->params.cb_vector;

    // u vector encoded with nBitsOfU * MLWE_POLYNOMIAL_COEFFICIENTS bits per polynomial
    let cb_u = (n_rows as usize) * (nBitsOfU as usize) * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);
    // v polynomial encoded with nBitsOfV * MLWE_POLYNOMIAL_COEFFICIENTS bits
    let cb_v = (nBitsOfV as usize) * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);

    if (cb_agreed_secret != SIZEOF_AGREED_SECRET) || (cb_ciphertext != cb_u + cb_v) {
        return Error::InvalidArgument;
    }

    let pvrInner = &mut p_comp_temps.abVectorBuffer0[0..n_rows as usize];
    let pv_tmp = &mut p_comp_temps.abVectorBuffer1[0..n_rows as usize];
    let pe_tmp0 = &mut p_comp_temps.abPolyElementBuffer0;
    let pe_tmp1 = &mut p_comp_temps.abPolyElementBuffer1;
    let pa_tmp = &mut p_comp_temps.abPolyElementAccumulatorBuffer;

    // CBDSampleBuffer = (K || rOuter) = SHA3-512(pb_random || encapsKeyHash)
    crate::hash::sha3_512_init(&mut p_comp_temps.hashState0);
    crate::hash::sha3_512_append(&mut p_comp_temps.hashState0, pb_random);
    crate::hash::sha3_512_append(&mut p_comp_temps.hashState0, &pk_mlkem_key.encaps_key_hash);
    // Note (Rust): should we have a type that is less strict for the output of sha3_512_result?
    // Note (Rust): no assert!(SIZEOF_AGREED_SECRET < SHA3_512_RESULT_SIZE)?
    crate::hash::sha3_512_result(
        &mut p_comp_temps.hashState0,
        (&mut CBDSampleBuffer[0..crate::hash::SHA3_512_RESULT_SIZE])
            .try_into()
            .unwrap(),
    );

    // Write K to pb_agreed_secret
    pb_agreed_secret[0..SIZEOF_AGREED_SECRET]
        .copy_from_slice(&CBDSampleBuffer[0..SIZEOF_AGREED_SECRET]);

    // Initialize p_shake_stateBase with rOuter
    crate::hash::shake256_init(&mut p_comp_temps.hashState0);
    crate::hash::shake256_append(
        &mut p_comp_temps.hashState0,
        &CBDSampleBuffer[cb_agreed_secret..cb_agreed_secret + 32],
    );

    // Expand rInner vector
    c_for!(let mut i=0u8; i<n_rows; i += 1;
    {
        CBDSampleBuffer[0] = i;
        crate::hash::shake256_state_copy( &mut p_comp_temps.hashState0, &mut p_comp_temps.hashState1 );
        crate::hash::shake256_append( &mut p_comp_temps.hashState1, &CBDSampleBuffer[0..1] );

        crate::hash::shake256_extract( &mut p_comp_temps.hashState1, &mut CBDSampleBuffer[0..64usize*(n_eta1 as usize)], false );

        SymCryptMlKemPolyElementSampleCBDFromBytes( & CBDSampleBuffer, n_eta1 as u32, &mut pvrInner[i as usize]);
    });

    // Perform NTT on rInner
    SymCryptMlKemVectorNTT(pvrInner);

    // Set pv_tmp to 0
    // TODO: write a helper function -- any way to do this better?
    pv_tmp.copy_from_slice(&vec![POLYELEMENT_ZERO; n_rows as usize].into_boxed_slice());
    // SymCryptMlKemVectorSetZero( pv_tmp );

    // pv_tmp = (Atranspose o rInner) ./ R
    SymCryptMlKemMatrixVectorMontMulAndAdd(
        pk_mlkem_key.atranspose_mut(),
        pvrInner,
        pv_tmp,
        pa_tmp,
        n_rows,
    );

    // pv_tmp = INTT(Atranspose o rInner)
    SymCryptMlKemVectorINTTAndMulR(pv_tmp);

    // Expand e1 and add it to pv_tmp - do addition PolyElement-wise to reduce memory usage
    c_for!(let mut i=0; i<n_rows; i += 1; {
        CBDSampleBuffer[0] = n_rows+i;
        crate::hash::shake256_state_copy( &mut p_comp_temps.hashState0, &mut p_comp_temps.hashState1 );
        crate::hash::shake256_append( &mut p_comp_temps.hashState1, &CBDSampleBuffer[0..1] );

        crate::hash::shake256_extract( &mut p_comp_temps.hashState1, &mut CBDSampleBuffer[0..64*(n_eta2 as usize)], false );

        SymCryptMlKemPolyElementSampleCBDFromBytes( &CBDSampleBuffer, n_eta2 as u32, pe_tmp0 );

        // Note (Rust): in-place operation here, was:
        // SymCryptMlKemPolyElementAdd( INTERNAL_MLKEM_VECTOR_ELEMENT(i, pv_tmp), pe_tmp0, INTERNAL_MLKEM_VECTOR_ELEMENT(i, pv_tmp) );
        // Added a copy -- TODO: measure performance impact of the copy
        let copy = pv_tmp[i as usize];
        SymCryptMlKemPolyElementAdd( &copy, pe_tmp0, &mut pv_tmp[i as usize] );

    });

    // pv_tmp = u = INTT(Atranspose o rInner) + e1
    // Compress and encode u into prefix of ciphertext
    SymCryptMlKemVectorCompressAndEncode(pv_tmp, nBitsOfU as u32, &mut pb_ciphertext[0..cb_u]);

    // pe_tmp0 = (t o r) ./ R
    SymCryptMlKemVectorMontDotProduct(pk_mlkem_key.t_mut(), pvrInner, pe_tmp0, pa_tmp);

    // pe_tmp0 = INTT(t o r)
    SymCryptMlKemPolyElementINTTAndMulR(pe_tmp0);

    // Expand e2 polynomial in pe_tmp1
    CBDSampleBuffer[0] = 2 * n_rows;
    crate::hash::shake256_state_copy(&mut p_comp_temps.hashState0, &mut p_comp_temps.hashState1);
    crate::hash::shake256_append(&mut p_comp_temps.hashState1, &CBDSampleBuffer[0..1]);

    crate::hash::shake256_extract(
        &mut p_comp_temps.hashState1,
        &mut CBDSampleBuffer[0..64 * (n_eta2 as usize)],
        false,
    );

    SymCryptMlKemPolyElementSampleCBDFromBytes(&mut CBDSampleBuffer, n_eta2 as u32, pe_tmp1);

    // peTmp = INTT(t o r) + e2
    // Note (Rust): in-place operation, was:
    // SymCryptMlKemPolyElementAdd( pe_tmp0, pe_tmp1, pe_tmp0 );
    // FIXME (measure performance issues, adjust)
    let copy = *pe_tmp0;
    SymCryptMlKemPolyElementAdd(&copy, pe_tmp1, pe_tmp0);

    // pe_tmp1 = mu
    SymCryptMlKemPolyElementDecodeAndDecompress(pb_random, 1, pe_tmp1);

    // pe_tmp0 = v = INTT(t o r) + e2 + mu
    let copy = *pe_tmp0;
    // FIXME (same as above)
    SymCryptMlKemPolyElementAdd(&copy, pe_tmp1, pe_tmp0);

    // Compress and encode v into remainder of ciphertext
    SymCryptMlKemPolyElementCompressAndEncode(pe_tmp0, nBitsOfV as u32, &mut pb_ciphertext[cb_u..]);

    // cleanup:
    //     SymCryptWipeKnownSize( CBDSampleBuffer, sizeof(CBDSampleBuffer) );

    Error::NoError
}

pub fn SymCryptMlKemEncapsulateEx(
    pk_mlkem_key: &mut Key,
    pb_random: &[u8], // Note(Rust): we could statically require the right length, and have the FFI
    // wrapper enforce it
    pb_agreed_secret: &mut [u8],
    pb_ciphertext: &mut [u8],
) -> Error {
    let cb_random = pb_random.len();
    // let cb_agreed_secret = pb_agreed_secret.len();
    // let cb_ciphertext = pb_ciphertext.len();

    if cb_random != SIZEOF_ENCAPS_RANDOM {
        return Error::InvalidArgument;
    }

    let p_comp_temps = Box::try_new(INTERNAL_COMPUTATION_TEMPORARIES {
        abVectorBuffer0: [POLYELEMENT_ZERO; MATRIX_MAX_NROWS],
        abVectorBuffer1: [POLYELEMENT_ZERO; MATRIX_MAX_NROWS],
        abPolyElementBuffer0: POLYELEMENT_ZERO,
        abPolyElementBuffer1: POLYELEMENT_ZERO,
        abPolyElementAccumulatorBuffer: [0; MLWE_POLYNOMIAL_COEFFICIENTS],
        hashState0: crate::hash::UNINITIALIZED_HASH_STATE,
        hashState1: crate::hash::UNINITIALIZED_HASH_STATE,
    });

    let mut p_comp_temps = match p_comp_temps {
        Result::Err(_) => return Error::MemoryAllocationFailure,
        Result::Ok(p_comp_temps) => p_comp_temps,
    };

    SymCryptMlKemEncapsulateInternal(
        pk_mlkem_key,
        pb_agreed_secret,
        pb_ciphertext,
        pb_random.try_into().unwrap(),
        &mut p_comp_temps,
    )
}

pub fn SymCryptMlKemEncapsulate(
    pk_mlkem_key: &mut Key,
    pb_agreed_secret: &mut [u8],
    pb_ciphertext: &mut [u8],
) -> Error {
    let mut pbm = [0u8; SIZEOF_ENCAPS_RANDOM];

    let sc_error = random(&mut pbm);
    if sc_error != Error::NoError {
        return sc_error;
    }

    SymCryptMlKemEncapsulateEx(pk_mlkem_key, &pbm, pb_agreed_secret, pb_ciphertext)
}

// cleanup:
//     SymCryptWipeKnownSize( pbm, sizeof(pbm) );

//     return sc_error;
// }

pub fn SymCryptMlKemDecapsulate(
    pk_mlkem_key: &mut Key,
    pb_ciphertext: &[u8],
    pb_agreed_secret: &mut [u8],
) -> Error {
    let cb_ciphertext = pb_ciphertext.len();
    let cb_agreed_secret = pb_agreed_secret.len();

    let p_comp_temps = Box::try_new(INTERNAL_COMPUTATION_TEMPORARIES {
        abVectorBuffer0: [POLYELEMENT_ZERO; MATRIX_MAX_NROWS],
        abVectorBuffer1: [POLYELEMENT_ZERO; MATRIX_MAX_NROWS],
        abPolyElementBuffer0: POLYELEMENT_ZERO,
        abPolyElementBuffer1: POLYELEMENT_ZERO,
        abPolyElementAccumulatorBuffer: [0; MLWE_POLYNOMIAL_COEFFICIENTS],
        hashState0: crate::hash::UNINITIALIZED_HASH_STATE,
        hashState1: crate::hash::UNINITIALIZED_HASH_STATE,
    });

    let mut p_comp_temps = match p_comp_temps {
        Result::Err(_) => return Error::MemoryAllocationFailure,
        Result::Ok(p_comp_temps) => p_comp_temps,
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
    // let pb_comp_ciphers = vec![0u8; 2*cb_ciphertext].into_boxed_slice();
    let pb_comp_ciphers = Vec::try_with_capacity(2 * cb_ciphertext);
    let mut pb_comp_ciphers = match pb_comp_ciphers {
        Result::Ok(pb_comp_ciphers) => pb_comp_ciphers,
        Result::Err(_) => return Error::MemoryAllocationFailure,
    };
    pb_comp_ciphers.resize(2 * cb_ciphertext, 0u8);
    let mut pb_comp_ciphers = pb_comp_ciphers.into_boxed_slice();
    let (pbReadCiphertext, pbReencapsulatedCiphertext) = pb_comp_ciphers.split_at_mut(cb_ciphertext);

    //     ERROR sc_error = NO_ERROR;
    //     SIZE_T cb_u, cb_v, cbCopy;
    //     PVECTOR pvu;
    //     PPOLYELEMENT pe_tmp0, pe_tmp1;
    //     PPOLYELEMENT_ACCUMULATOR pa_tmp;
    //     PSHAKE256_STATE p_shake_state;
    let n_rows = pk_mlkem_key.params.n_rows;
    let nBitsOfU = pk_mlkem_key.params.n_bits_of_u;
    let nBitsOfV = pk_mlkem_key.params.n_bits_of_v;
    // let cbPolyElement = pk_mlkem_key.params.cbPolyElement;
    // let cb_vector = pk_mlkem_key.params.cb_vector;

    // u vector encoded with nBitsOfU * MLWE_POLYNOMIAL_COEFFICIENTS bits per polynomial
    let cb_u = n_rows as usize * nBitsOfU as usize * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);
    // v polynomial encoded with nBitsOfV * MLWE_POLYNOMIAL_COEFFICIENTS bits
    let cb_v = nBitsOfV as usize * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);

    if (cb_agreed_secret != SIZEOF_AGREED_SECRET)
        || (cb_ciphertext != cb_u + cb_v)
        || !pk_mlkem_key.has_private_key
    {
        return Error::InvalidArgument;
    }

    // Read the input ciphertext once to local pbReadCiphertext to ensure our view of ciphertext consistent
    pbReadCiphertext.copy_from_slice(pb_ciphertext);

    let pvu = &mut p_comp_temps.abVectorBuffer0[0..n_rows as usize];
    let pe_tmp0 = &mut p_comp_temps.abPolyElementBuffer0;
    let pe_tmp1 = &mut p_comp_temps.abPolyElementBuffer1;
    let pa_tmp = &mut p_comp_temps.abPolyElementAccumulatorBuffer;

    // Decode and decompress u
    let sc_error =
        SymCryptMlKemVectorDecodeAndDecompress(&mut pbReadCiphertext[0..cb_u], nBitsOfU as u32, pvu);
    assert!(sc_error == Error::NoError);

    // Perform NTT on u
    SymCryptMlKemVectorNTT(pvu);

    // pe_tmp0 = (s o NTT(u)) ./ R
    SymCryptMlKemVectorMontDotProduct(pk_mlkem_key.s_mut(), pvu, pe_tmp0, pa_tmp);

    // pe_tmp0 = INTT(s o NTT(u))
    SymCryptMlKemPolyElementINTTAndMulR(pe_tmp0);

    // Decode and decompress v
    let sc_error = SymCryptMlKemPolyElementDecodeAndDecompress(
        &mut pbReadCiphertext[cb_u..],
        nBitsOfV as u32,
        pe_tmp1,
    );
    assert!(sc_error == Error::NoError);

    // pe_tmp0 = w = v - INTT(s o NTT(u))
    // FIXME
    let copy = *pe_tmp0;
    SymCryptMlKemPolyElementSub(pe_tmp1, &copy, pe_tmp0);

    // pbDecryptedRandom = m' = Encoding of w
    SymCryptMlKemPolyElementCompressAndEncode(pe_tmp0, 1, &mut pbDecryptedRandom);

    // Compute:
    //  pbDecapsulatedSecret = K' = Decapsulated secret (without implicit rejection)
    //  pbReencapsulatedCiphertext = c' = Ciphertext from re-encapsulating decrypted random value
    let sc_error = SymCryptMlKemEncapsulateInternal(
        pk_mlkem_key,
        &mut pbDecapsulatedSecret,
        pbReencapsulatedCiphertext,
        &mut pbDecryptedRandom,
        &mut p_comp_temps,
    );
    assert!(sc_error == Error::NoError);

    // Compute the secret we will return if using implicit rejection
    // pbImplicitRejectionSecret = K_bar = SHAKE256( z || c )
    let p_shake_state = &mut p_comp_temps.hashState0;
    crate::hash::shake256_init(p_shake_state);
    crate::hash::shake256_append(p_shake_state, &pk_mlkem_key.private_random);
    crate::hash::shake256_append(p_shake_state, pbReadCiphertext);
    crate::hash::shake256_extract(p_shake_state, &mut pbImplicitRejectionSecret, false);

    // Constant time test if re-encryption successful
    let successfulReencrypt = pbReencapsulatedCiphertext == pbReadCiphertext;

    // If not successful, perform side-channel-safe copy of Implicit Rejection secret over Decapsulated secret
    let cbCopy = ((successfulReencrypt as usize).wrapping_sub(1)) & SIZEOF_AGREED_SECRET;
    pbDecapsulatedSecret[0..cbCopy].copy_from_slice(&pbImplicitRejectionSecret[0..cbCopy]);
    // FIXME, was:
    // SymCryptScsCopy( pbImplicitRejectionSecret, cbCopy, pbDecapsulatedSecret, SIZEOF_AGREED_SECRET );

    // Write agreed secret (with implicit rejection) to pb_agreed_secret
    pb_agreed_secret.copy_from_slice(&pbDecapsulatedSecret);

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
