//
// mlkem.c   ML-KEM related functionality
//
// Copyright (c) Microsoft Corporation. Licensed under the MIT license.
//

use crate::ntt::*;
use crate::key::*;

use crate::c_for;

const fn SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(_nRows: usize) -> usize { 384 * _nRows }

// d and z are each 32 bytes
const SIZEOF_FORMAT_PRIVATE_SEED: usize =               2*32;
// s and t are encoded uncompressed vectors
// public seed, H(encapsulation key) and z are each 32 bytes
const fn SIZEOF_FORMAT_DECAPSULATION_KEY(_nRows: usize) -> usize {
    2*SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(_nRows) + 3*32
}
// t is encoded uncompressed vector
// public seed is 32 bytes
const fn SIZEOF_FORMAT_ENCAPSULATION_KEY(_nRows: usize) -> usize {
    SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(_nRows) + 32
}

const CIPHERTEXT_SIZE_MLKEM512  : usize = 768 ;
const CIPHERTEXT_SIZE_MLKEM768  : usize = 1088;
const CIPHERTEXT_SIZE_MLKEM1024 : usize = 1568;

// MLKEM key formats
// ==================
//  -   The below formats apply **only to external formats**: When somebody is
//      importing a key (from test vectors, for example) or exporting a key.
//      The internal format of the keys is not visible to the caller.
enum MLKEMKEY_FORMAT {
        // Note (Rust): skipping NULL case since these things are exhaustive, but keeping the
        // values for ease of debug / differential testing
    PRIVATE_SEED       = 1,    
        // 64-byte concatenation of d || z from FIPS 203. Smallest representation of a full
        // ML-KEM key.
        // On its own it is ambiguous what type of ML-KEM key this represents; callers wanting to
        // store this format must track the key type alongside the key.
    DECAPSULATION_KEY  = 2,
        // Standard byte encoding of an ML-KEM Decapsulation key, per FIPS 203.
        // Size is 1632, 2400, or 3168 bytes for ML-KEM 512, 768, and 1024 respectively.
    ENCAPSULATION_KEY  = 3,
        // Standard byte encoding of an ML-KEM Encapsulation key, per FIPS 203.
        // Size is 800, 1184, or 1568 bytes for ML-KEM 512, 768, and 1024 respectively.
}

fn SymCryptMlKemSizeofKeyFormatFromParams(params: PARAMS,
            mlKemkeyFormat: MLKEMKEY_FORMAT) -> usize
{
    let internalParams = SymCryptMlKemkeyGetInternalParamsFromParams(params);

    match mlKemkeyFormat
    {
        MLKEMKEY_FORMAT::PRIVATE_SEED => SIZEOF_FORMAT_PRIVATE_SEED,
        MLKEMKEY_FORMAT::DECAPSULATION_KEY => SIZEOF_FORMAT_DECAPSULATION_KEY(internalParams.nRows as usize),
        MLKEMKEY_FORMAT::ENCAPSULATION_KEY => SIZEOF_FORMAT_ENCAPSULATION_KEY(internalParams.nRows as usize),
    }
}

fn SymCryptMlKemSizeofCiphertextFromParams(
    params: PARAMS
) -> usize
{
    let internalParams = SymCryptMlKemkeyGetInternalParamsFromParams(params);

    // u vector encoded with nBitsOfU * MLWE_POLYNOMIAL_COEFFICIENTS bits per polynomial
    let cbU = (internalParams.nRows as usize) * (internalParams.nBitsOfU as usize) * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);
    // v polynomial encoded with nBitsOfV * MLWE_POLYNOMIAL_COEFFICIENTS bits
    let cbV = (internalParams.nBitsOfV as usize) * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);

    assert!( (internalParams.params != PARAMS::MLKEM512)  || ((cbU + cbV) == CIPHERTEXT_SIZE_MLKEM512)  );
    assert!( (internalParams.params != PARAMS::MLKEM768)  || ((cbU + cbV) == CIPHERTEXT_SIZE_MLKEM768)  );
    assert!( (internalParams.params != PARAMS::MLKEM1024) || ((cbU + cbV) == CIPHERTEXT_SIZE_MLKEM1024) );

    cbU + cbV
}

fn SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed(
    pkMlKemkey: & mut KEY,
    pCompTemps: & mut INTERNAL_COMPUTATION_TEMPORARIES)
{
    let mut coordinates = [0u8; 2];

    let pShakeStateBase = &mut pCompTemps.hashState0;
    let pShakeStateWork = &mut pCompTemps.hashState1;
    let nRows = pkMlKemkey.params.nRows;

    crate::hash::shake128_init( pShakeStateBase );
    crate::hash::shake128_append(pShakeStateBase, &pkMlKemkey.publicSeed);

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

fn
SymCryptMlKemkeyComputeEncapsulationKeyHash(
    pkMlKemkey: &mut KEY,
    pCompTemps: &mut INTERNAL_COMPUTATION_TEMPORARIES,
    cbEncodedVector: usize )
{
    let pState = &mut pCompTemps.hashState0;

    crate::hash::sha3_256_init( pState );
    crate::hash::sha3_256_append( pState, &pkMlKemkey.encodedT);
    crate::hash::sha3_256_append( pState, &pkMlKemkey.publicSeed);
    crate::hash::sha3_256_result( pState, &mut pkMlKemkey.encapsKeyHash );
}

fn
SymCryptMlKemkeyExpandFromPrivateSeed(
    pkMlKemkey: &mut KEY,
    pCompTemps: &mut INTERNAL_COMPUTATION_TEMPORARIES )
{
    let mut privateSeedHash = [0u8; crate::hash::SHA3_512_RESULT_SIZE];
    let mut CBDSampleBuffer = [0u8; 3*64 + 1];
    // PVECTOR pvTmp;
    // PPOLYELEMENT_ACCUMULATOR paTmp;
    // UINT32 i;
    let nRows = pkMlKemkey.params.nRows;
    let nEta1 = pkMlKemkey.params.nEta1;
    let cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(nRows as usize);
    // const SIZE_T cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(nRows);
    // const UINT32 cbPolyElement = pkMlKemkey->params.cbPolyElement;
    // const UINT32 cbVector = pkMlKemkey->params.cbVector;

    assert!( pkMlKemkey.hasPrivateSeed );
    assert!( (nEta1 == 2) || (nEta1 == 3) );

    // Note(Rust): there's a whole lot of NULL-checking going on in C, which presumably does not
    // happen here -- the checks for NULL in the C code seem to be unreachable, because at the
    // leaves, SymCryptPolyElementCreate cannot return NULL...?

    // (rho || sigma) = G(d || k)
    // use CBDSampleBuffer to concatenate the private seed and encoding of nRows
    CBDSampleBuffer[0..pkMlKemkey.privateSeed.len()].copy_from_slice(&pkMlKemkey.privateSeed);
    CBDSampleBuffer[pkMlKemkey.privateSeed.len() /* == 32 */] = nRows;
    crate::hash::sha3_512(&CBDSampleBuffer[0..pkMlKemkey.privateSeed.len()+1], &mut privateSeedHash);

    // copy public seed
    pkMlKemkey.publicSeed.copy_from_slice(&privateSeedHash);

    // generate A from public seed
    SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed( pkMlKemkey, pCompTemps );

    // Initialize pShakeStateBase with sigma
    crate::hash::shake256_init(&mut pCompTemps.hashState0);
    crate::hash::shake256_append(&mut pCompTemps.hashState0, &privateSeedHash[pkMlKemkey.publicSeed.len()..pkMlKemkey.publicSeed.len()+32]);

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
    SymCryptMlKemVectorNTT( pkMlKemkey.s_mut() );
    SymCryptMlKemVectorNTT( pkMlKemkey.t_mut() );

    // pvTmp = s .* R
    SymCryptMlKemVectorMulR( pkMlKemkey.s_mut(), &mut pCompTemps.abVectorBuffer0 );

    // t = ((A o (s .* R)) ./ R) + e = A o s + e
    let (a, _, t) = pkMlKemkey.ast_mut();
    SymCryptMlKemMatrixVectorMontMulAndAdd(a, &pCompTemps.abVectorBuffer0, t, &mut pCompTemps.abPolyElementAccumulatorBuffer, nRows);

    // transpose A
    SymCryptMlKemMatrixTranspose( pkMlKemkey.atranspose_mut(), nRows);

    // precompute byte-encoding of public vector t
    let (t, encodedT) = pkMlKemkey.t_encoded_t_mut();
    SymCryptMlKemVectorCompressAndEncode(t, 12, &mut encodedT[0..cbEncodedVector] );

    // precompute hash of encapsulation key blob
    SymCryptMlKemkeyComputeEncapsulationKeyHash( pkMlKemkey, pCompTemps, cbEncodedVector );

    // Cleanup!
    // FIXME
    // SymCryptWipeKnownSize( privateSeedHash, sizeof(privateSeedHash) );
    // SymCryptWipeKnownSize( CBDSampleBuffer, sizeof(CBDSampleBuffer) );
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

fn
SymCryptMlKemkeySetValue(
    pbSrc: &[u8],
    mlKemkeyFormat: MLKEMKEY_FORMAT,
    flags: u32,
    pkMlKemkey: &mut KEY ) -> MLKEM_ERROR
{
    // ERROR scError = NO_ERROR;
    let mut pbCurr: usize = 0;
    // PINTERNAL_COMPUTATION_TEMPORARIES pCompTemps = NULL;
    let nRows = pkMlKemkey.params.nRows;
    let cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR( nRows as usize);

    // Ensure only allowed flags are specified
    let allowedFlags: u32 = FLAG_KEY_NO_FIPS | FLAG_KEY_MINIMAL_VALIDATION;

    if ( ( flags & !allowedFlags ) != 0 )
    {
        return MLKEM_ERROR::INVALID_ARGUMENT;
    }

    // Check that minimal validation flag only specified with no fips
    if ( ( flags & FLAG_KEY_NO_FIPS ) == 0 ) &&
         ( ( flags & FLAG_KEY_MINIMAL_VALIDATION ) != 0 )
    {
        return MLKEM_ERROR::INVALID_ARGUMENT;
    }

    // Note (Rust): ruled out by typing
    // if( mlKemkeyFormat == MLKEMKEY_FORMAT_NULL )
    // {
    //     return MLKEM_ERROR::INVALID_ARGUMENT;
    // }

    if( ( flags & FLAG_KEY_NO_FIPS ) == 0 )
    {
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
        abPolyElementAccumulatorBuffer: [0; MLWE_POLYNOMIAL_COEFFICIENTS ],
        hashState0: crate::hash::UNINITIALIZED_HASH_STATE,
        hashState1: crate::hash::UNINITIALIZED_HASH_STATE,
    });

    let mut pCompTemps = match pCompTemps {
        Result::Err(_) => { return MLKEM_ERROR::MEMORY_ALLOCATION_FAILURE },
        Result::Ok(pCompTemps) => pCompTemps
    };

    match mlKemkeyFormat {
    MLKEMKEY_FORMAT::PRIVATE_SEED =>
    {
        if( pbSrc.len() != SIZEOF_FORMAT_PRIVATE_SEED )
        {
            return MLKEM_ERROR::WRONG_KEY_SIZE;
        }

        pkMlKemkey.hasPrivateSeed = true;
        let l = pkMlKemkey.privateSeed.len();
        pkMlKemkey.privateSeed.copy_from_slice(&pbSrc[0..l]);
        pbCurr += pkMlKemkey.privateSeed.len();

        pkMlKemkey.hasPrivateKey = true;
        let l = pkMlKemkey.privateRandom.len();
        pkMlKemkey.privateRandom.copy_from_slice(&pbSrc[pbCurr..pbCurr+l]);
        pbCurr += pkMlKemkey.privateRandom.len();

        SymCryptMlKemkeyExpandFromPrivateSeed( pkMlKemkey, &mut pCompTemps );
    },

    MLKEMKEY_FORMAT::DECAPSULATION_KEY =>
    {
        if( pbSrc.len() != SIZEOF_FORMAT_DECAPSULATION_KEY( nRows as usize) )
        {
            return MLKEM_ERROR::WRONG_KEY_SIZE;
        }

        // decode s
        let scError = SymCryptMlKemVectorDecodeAndDecompress( &pbSrc[pbCurr..pbCurr+cbEncodedVector], 12, pkMlKemkey.s_mut() );
        if scError != MLKEM_ERROR::NO_ERROR
        {
            return scError;
        }
        pbCurr += cbEncodedVector;

        // copy t and decode t
        pkMlKemkey.encodedT.copy_from_slice(&pbSrc[pbCurr..pbCurr+cbEncodedVector]);
        pbCurr += cbEncodedVector;
        let (t, encodedT) = pkMlKemkey.t_encoded_t_mut();
        let scError = SymCryptMlKemVectorDecodeAndDecompress( &encodedT[0..cbEncodedVector], 12, t );
        if( scError != MLKEM_ERROR::NO_ERROR )
        {
            return scError;
        }

        // copy public seed and expand public matrix
        let l = pkMlKemkey.publicSeed.len();
        pkMlKemkey.publicSeed.copy_from_slice(&pbSrc[pbCurr..pbCurr+l] );
        pbCurr += pkMlKemkey.publicSeed.len();
        SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed( pkMlKemkey, &mut pCompTemps );

        // transpose A
        SymCryptMlKemMatrixTranspose( pkMlKemkey.atranspose_mut(), nRows );

        // copy hash of encapsulation key
        let l = pkMlKemkey.encapsKeyHash.len();
        pkMlKemkey.encapsKeyHash.copy_from_slice(&pbSrc[pbCurr..pbCurr+l]);
        pbCurr += pkMlKemkey.encapsKeyHash.len();

        // copy private random
        let l = pkMlKemkey.privateRandom.len();
        pkMlKemkey.privateRandom.copy_from_slice(&pbSrc[pbCurr..pbCurr+l]);
        pbCurr += pkMlKemkey.privateRandom.len();

        pkMlKemkey.hasPrivateSeed = false;
        pkMlKemkey.hasPrivateKey  = true;
    },

    MLKEMKEY_FORMAT::ENCAPSULATION_KEY =>
    {
        if( pbSrc.len() != SIZEOF_FORMAT_ENCAPSULATION_KEY( nRows as usize) )
        {
            return MLKEM_ERROR::WRONG_KEY_SIZE;
        }

        // copy t and decode t
        pkMlKemkey.encodedT.copy_from_slice(&pbSrc[pbCurr..pbCurr+cbEncodedVector]);
        pbCurr += cbEncodedVector;
        let (t, encodedT) = pkMlKemkey.t_encoded_t_mut();
        let scError = SymCryptMlKemVectorDecodeAndDecompress( &encodedT[0..cbEncodedVector], 12, t );
        if( scError != MLKEM_ERROR::NO_ERROR )
        {
            return scError;
        }

        // copy public seed and expand public matrix
        let l = pkMlKemkey.publicSeed.len();
        pkMlKemkey.publicSeed.copy_from_slice(&pbSrc[pbCurr..pbCurr+l]);
        pbCurr += pkMlKemkey.publicSeed.len();
        SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed( pkMlKemkey, &mut pCompTemps );

        // transpose A
        SymCryptMlKemMatrixTranspose( pkMlKemkey.atranspose_mut(), nRows );

        // precompute hash of encapsulation key blob
        SymCryptMlKemkeyComputeEncapsulationKeyHash( pkMlKemkey, &mut pCompTemps, cbEncodedVector );

        pkMlKemkey.hasPrivateSeed = false;
        pkMlKemkey.hasPrivateKey  = false;
    }
    };
    MLKEM_ERROR::NO_ERROR
    // Note (Rust): exhaustiveness
    // else
    // {
    //     scError = NOT_IMPLEMENTED;
    //     goto cleanup;
    // }

//     ASSERT( pbCurr == pbSrc + cbSrc );

// cleanup:
//     if( pCompTemps != NULL )
//     {
//         SymCryptWipe( pCompTemps, sizeof(*pCompTemps) );
//         SymCryptCallbackFree( pCompTemps );
//     }

//     return scError;
}


// ERROR
// CALL
// SymCryptMlKemkeyGetValue(
//     _In_                        PCMLKEMKEY         pkMlKemkey,
//     _Out_writes_bytes_( cbDst ) PBYTE                       pbDst,
//                                 SIZE_T                      cbDst,
//                                 MLKEMKEY_FORMAT    mlKemkeyFormat,
//                                 UINT32                      flags )
// {
//     ERROR scError = NO_ERROR;
//     PBYTE pbCurr = pbDst;
//     const UINT32 nRows = pkMlKemkey->params.nRows;
//     const SIZE_T cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR( nRows );

//     UNREFERENCED_PARAMETER( flags );

//     if( mlKemkeyFormat == MLKEMKEY_FORMAT_NULL )
//     {
//         scError = INVALID_ARGUMENT;
//         goto cleanup;
//     }

//     if( mlKemkeyFormat == MLKEMKEY_FORMAT_PRIVATE_SEED )
//     {
//         if( cbDst != SIZEOF_FORMAT_PRIVATE_SEED )
//         {
//             scError = WRONG_KEY_SIZE;
//             goto cleanup;
//         }

//         if( !pkMlKemkey->hasPrivateSeed )
//         {
//             scError = INCOMPATIBLE_FORMAT;
//             goto cleanup;
//         }

//         memcpy( pbCurr, pkMlKemkey->privateSeed, sizeof(pkMlKemkey->privateSeed) );
//         pbCurr += sizeof(pkMlKemkey->privateSeed);

//         memcpy( pbCurr, pkMlKemkey->privateRandom, sizeof(pkMlKemkey->privateRandom) );
//         pbCurr += sizeof(pkMlKemkey->privateRandom);
//     }
//     else if( mlKemkeyFormat == MLKEMKEY_FORMAT_DECAPSULATION_KEY )
//     {
//         if( cbDst != SIZEOF_FORMAT_DECAPSULATION_KEY( nRows ) )
//         {
//             scError = INVALID_ARGUMENT;
//             goto cleanup;
//         }

//         if( !pkMlKemkey->hasPrivateKey )
//         {
//             scError = INVALID_ARGUMENT;
//             goto cleanup;
//         }

//         // We don't precompute byte-encoding of private key as exporting decapsulation key is not a critical path operation
//         // All other fields are kept in memory
//         SymCryptMlKemVectorCompressAndEncode( pkMlKemkey->pvs, 12, pbCurr, cbEncodedVector );
//         pbCurr += cbEncodedVector;

//         memcpy( pbCurr, pkMlKemkey->encodedT, cbEncodedVector );
//         pbCurr += cbEncodedVector;

//         memcpy( pbCurr, pkMlKemkey->publicSeed, sizeof(pkMlKemkey->publicSeed) );
//         pbCurr += sizeof(pkMlKemkey->publicSeed);

//         memcpy( pbCurr, pkMlKemkey->encapsKeyHash, sizeof(pkMlKemkey->encapsKeyHash) );
//         pbCurr += sizeof(pkMlKemkey->encapsKeyHash);

//         memcpy( pbCurr, pkMlKemkey->privateRandom, sizeof(pkMlKemkey->privateRandom) );
//         pbCurr += sizeof(pkMlKemkey->privateRandom);
//     }
//     else if( mlKemkeyFormat == MLKEMKEY_FORMAT_ENCAPSULATION_KEY )
//     {
//         if( cbDst != SIZEOF_FORMAT_ENCAPSULATION_KEY( nRows ) )
//         {
//             scError = INVALID_ARGUMENT;
//             goto cleanup;
//         }

//         memcpy( pbCurr, pkMlKemkey->encodedT, cbEncodedVector );
//         pbCurr += cbEncodedVector;

//         memcpy( pbCurr, pkMlKemkey->publicSeed, sizeof(pkMlKemkey->publicSeed) );
//         pbCurr += sizeof(pkMlKemkey->publicSeed);
//     }
//     else
//     {
//         scError = NOT_IMPLEMENTED;
//         goto cleanup;
//     }

//     ASSERT( pbCurr == pbDst + cbDst );

// cleanup:
//     return scError;
// }


// ERROR
// CALL
// SymCryptMlKemkeyGenerate(
//     _Inout_                     PMLKEMKEY  pkMlKemkey,
//                                 UINT32              flags )
// {
//     ERROR scError = NO_ERROR;
//     BYTE privateSeed[SIZEOF_FORMAT_PRIVATE_SEED];

//     // Ensure only allowed flags are specified
//     UINT32 allowedFlags = FLAG_KEY_NO_FIPS;

//     if ( ( flags & ~allowedFlags ) != 0 )
//     {
//         scError = INVALID_ARGUMENT;
//         goto cleanup;
//     }

//     scError = SymCryptCallbackRandom( privateSeed, sizeof(privateSeed) );
//     if( scError != NO_ERROR )
//     {
//         goto cleanup;
//     }

//     scError = SymCryptMlKemkeySetValue( privateSeed, sizeof(privateSeed), MLKEMKEY_FORMAT_PRIVATE_SEED, flags, pkMlKemkey );
//     if( scError != NO_ERROR )
//     {
//         goto cleanup;
//     }

//     // SymCryptMlKemkeySetValue ensures the self-test is run before
//     // first operational use of MlKem

//     // Awaiting feedback from NIST for discussion from PQC forum and CMUF
//     // before implementing costly PCT on ML-KEM key generation which is
//     // not expected by FIPS 203

// cleanup:
//     SymCryptWipeKnownSize( privateSeed, sizeof(privateSeed) );

//     return scError;
// }

// ERROR
// CALL
// SymCryptMlKemEncapsulateInternal(
//     _In_    PCMLKEMKEY                                 pkMlKemkey,
//     _Out_writes_bytes_( cbAgreedSecret )
//             PBYTE                                               pbAgreedSecret,
//             SIZE_T                                              cbAgreedSecret,
//     _Out_writes_bytes_( cbCiphertext )
//             PBYTE                                               pbCiphertext,
//             SIZE_T                                              cbCiphertext,
//     _In_reads_bytes_( SIZEOF_ENCAPS_RANDOM )
//             PCBYTE                                              pbRandom,
//     _Inout_ PINTERNAL_COMPUTATION_TEMPORARIES    pCompTemps )
// {
//     BYTE CBDSampleBuffer[3*64 + 1];
//     ERROR scError = NO_ERROR;
//     PVECTOR pvrInner;
//     PVECTOR pvTmp;
//     PPOLYELEMENT peTmp0, peTmp1;
//     PPOLYELEMENT_ACCUMULATOR paTmp;
//     PSHA3_512_STATE pHashState = &pCompTemps->hashState0.sha3_512State;
//     PSHAKE256_STATE pShakeBaseState = &pCompTemps->hashState0.shake256State;
//     PSHAKE256_STATE pShakeWorkState = &pCompTemps->hashState1.shake256State;
//     SIZE_T cbU, cbV;
//     UINT32 i;
//     const UINT32 nRows = pkMlKemkey->params.nRows;
//     const UINT32 nBitsOfU = pkMlKemkey->params.nBitsOfU;
//     const UINT32 nBitsOfV = pkMlKemkey->params.nBitsOfV;
//     const UINT32 nEta1 = pkMlKemkey->params.nEta1;
//     const UINT32 nEta2 = pkMlKemkey->params.nEta2;
//     const UINT32 cbPolyElement = pkMlKemkey->params.cbPolyElement;
//     const UINT32 cbVector = pkMlKemkey->params.cbVector;

//     // u vector encoded with nBitsOfU * MLWE_POLYNOMIAL_COEFFICIENTS bits per polynomial
//     cbU = nRows * nBitsOfU * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);
//     // v polynomial encoded with nBitsOfV * MLWE_POLYNOMIAL_COEFFICIENTS bits
//     cbV = nBitsOfV * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);

//     if( (cbAgreedSecret != SIZEOF_AGREED_SECRET) ||
//         (cbCiphertext != cbU + cbV) )
//     {
//         scError = INVALID_ARGUMENT;
//         goto cleanup;
//     }

//     pvrInner = SymCryptMlKemVectorCreate( pCompTemps->abVectorBuffer0, cbVector, nRows );
//     ASSERT( pvrInner != NULL );
//     pvTmp = SymCryptMlKemVectorCreate( pCompTemps->abVectorBuffer1, cbVector, nRows );
//     ASSERT( pvTmp != NULL );
//     peTmp0 = SymCryptMlKemPolyElementCreate( pCompTemps->abPolyElementBuffer0, cbPolyElement );
//     ASSERT( peTmp0 != NULL );
//     peTmp1 = SymCryptMlKemPolyElementCreate( pCompTemps->abPolyElementBuffer1, cbPolyElement );
//     ASSERT( peTmp1 != NULL );
//     paTmp = SymCryptMlKemPolyElementAccumulatorCreate( pCompTemps->abPolyElementAccumulatorBuffer, 2*cbPolyElement );
//     ASSERT( paTmp != NULL );

//     // CBDSampleBuffer = (K || rOuter) = SHA3-512(pbRandom || encapsKeyHash)
//     SymCryptSha3_512Init( pHashState );
//     SymCryptSha3_512Append( pHashState, pbRandom, SIZEOF_ENCAPS_RANDOM );
//     SymCryptSha3_512Append( pHashState, pkMlKemkey->encapsKeyHash, sizeof(pkMlKemkey->encapsKeyHash) );
//     SymCryptSha3_512Result( pHashState, CBDSampleBuffer );

//     // Write K to pbAgreedSecret
//     memcpy( pbAgreedSecret, CBDSampleBuffer, SIZEOF_AGREED_SECRET );

//     // Initialize pShakeStateBase with rOuter
//     SymCryptShake256Init( pShakeBaseState );
//     SymCryptShake256Append( pShakeBaseState, CBDSampleBuffer+cbAgreedSecret, 32 );

//     // Expand rInner vector
//     for( i=0; i<nRows; i++ )
//     {
//         CBDSampleBuffer[0] = (BYTE) i;
//         SymCryptShake256StateCopy( pShakeBaseState, pShakeWorkState );
//         SymCryptShake256Append( pShakeWorkState, CBDSampleBuffer, 1 );

//         SymCryptShake256Extract( pShakeWorkState, CBDSampleBuffer, 64ul*nEta1, FALSE );

//         SymCryptMlKemPolyElementSampleCBDFromBytes( CBDSampleBuffer, nEta1, INTERNAL_MLKEM_VECTOR_ELEMENT(i, pvrInner) );
//     }

//     // Perform NTT on rInner
//     SymCryptMlKemVectorNTT( pvrInner );

//     // Set pvTmp to 0
//     SymCryptMlKemVectorSetZero( pvTmp );

//     // pvTmp = (Atranspose o rInner) ./ R
//     SymCryptMlKemMatrixVectorMontMulAndAdd( pkMlKemkey->pmAtranspose, pvrInner, pvTmp, paTmp );

//     // pvTmp = INTT(Atranspose o rInner)
//     SymCryptMlKemVectorINTTAndMulR( pvTmp );

//     // Expand e1 and add it to pvTmp - do addition PolyElement-wise to reduce memory usage
//     for( i=0; i<nRows; i++ )
//     {
//         CBDSampleBuffer[0] = (BYTE) (nRows+i);
//         SymCryptShake256StateCopy( pShakeBaseState, pShakeWorkState );
//         SymCryptShake256Append( pShakeWorkState, CBDSampleBuffer, 1 );

//         SymCryptShake256Extract( pShakeWorkState, CBDSampleBuffer, 64ul*nEta2, FALSE );

//         SymCryptMlKemPolyElementSampleCBDFromBytes( CBDSampleBuffer, nEta2, peTmp0 );

//         SymCryptMlKemPolyElementAdd( INTERNAL_MLKEM_VECTOR_ELEMENT(i, pvTmp), peTmp0, INTERNAL_MLKEM_VECTOR_ELEMENT(i, pvTmp) );
//     }

//     // pvTmp = u = INTT(Atranspose o rInner) + e1
//     // Compress and encode u into prefix of ciphertext
//     SymCryptMlKemVectorCompressAndEncode( pvTmp, nBitsOfU, pbCiphertext, cbU );

//     // peTmp0 = (t o r) ./ R
//     SymCryptMlKemVectorMontDotProduct( pkMlKemkey->pvt, pvrInner, peTmp0, paTmp );

//     // peTmp0 = INTT(t o r)
//     SymCryptMlKemPolyElementINTTAndMulR( peTmp0 );

//     // Expand e2 polynomial in peTmp1
//     CBDSampleBuffer[0] = (BYTE) (2*nRows);
//     SymCryptShake256StateCopy( pShakeBaseState, pShakeWorkState );
//     SymCryptShake256Append( pShakeWorkState, CBDSampleBuffer, 1 );

//     SymCryptShake256Extract( pShakeWorkState, CBDSampleBuffer, 64ul*nEta2, FALSE );

//     SymCryptMlKemPolyElementSampleCBDFromBytes( CBDSampleBuffer, nEta2, peTmp1 );

//     // peTmp = INTT(t o r) + e2
//     SymCryptMlKemPolyElementAdd( peTmp0, peTmp1, peTmp0 );

//     // peTmp1 = mu
//     SymCryptMlKemPolyElementDecodeAndDecompress( pbRandom, 1, peTmp1 );

//     // peTmp0 = v = INTT(t o r) + e2 + mu
//     SymCryptMlKemPolyElementAdd( peTmp0, peTmp1, peTmp0 );

//     // Compress and encode v into remainder of ciphertext
//     SymCryptMlKemPolyElementCompressAndEncode( peTmp0, nBitsOfV, pbCiphertext+cbU );

// cleanup:
//     SymCryptWipeKnownSize( CBDSampleBuffer, sizeof(CBDSampleBuffer) );

//     return scError;
// }


// ERROR
// CALL
// SymCryptMlKemEncapsulateEx(
//     _In_                                    PCMLKEMKEY pkMlKemkey,
//     _In_reads_bytes_( cbRandom )            PCBYTE              pbRandom,
//                                             SIZE_T              cbRandom,
//     _Out_writes_bytes_( cbAgreedSecret )    PBYTE               pbAgreedSecret,
//                                             SIZE_T              cbAgreedSecret,
//     _Out_writes_bytes_( cbCiphertext )      PBYTE               pbCiphertext,
//                                             SIZE_T              cbCiphertext )
// {
//     ERROR scError = NO_ERROR;
//     PINTERNAL_COMPUTATION_TEMPORARIES pCompTemps = NULL;

//     if( cbRandom != SIZEOF_ENCAPS_RANDOM )
//     {
//         scError = INVALID_ARGUMENT;
//         goto cleanup;
//     }

//     pCompTemps = SymCryptCallbackAlloc( sizeof(INTERNAL_COMPUTATION_TEMPORARIES) );
//     if( pCompTemps == NULL )
//     {
//         scError = MEMORY_ALLOCATION_FAILURE;
//         goto cleanup;
//     }

//     scError = SymCryptMlKemEncapsulateInternal(
//         pkMlKemkey,
//         pbAgreedSecret, cbAgreedSecret,
//         pbCiphertext, cbCiphertext,
//         pbRandom,
//         pCompTemps );

// cleanup:
//     if( pCompTemps != NULL )
//     {
//         SymCryptWipe( pCompTemps, sizeof(*pCompTemps) );
//         SymCryptCallbackFree( pCompTemps );
//     }

//     return scError;
// }

// ERROR
// CALL
// SymCryptMlKemEncapsulate(
//     _In_                                    PCMLKEMKEY pkMlKemkey,
//     _Out_writes_bytes_( cbAgreedSecret )    PBYTE               pbAgreedSecret,
//                                             SIZE_T              cbAgreedSecret,
//     _Out_writes_bytes_( cbCiphertext )      PBYTE               pbCiphertext,
//                                             SIZE_T              cbCiphertext )
// {
//     ERROR scError = NO_ERROR;
//     BYTE pbm[SIZEOF_ENCAPS_RANDOM];

//     scError = SymCryptCallbackRandom( pbm, sizeof(pbm) );
//     if( scError != NO_ERROR )
//     {
//         goto cleanup;
//     }

//     scError = SymCryptMlKemEncapsulateEx(
//         pkMlKemkey,
//         pbm, sizeof(pbm),
//         pbAgreedSecret, cbAgreedSecret,
//         pbCiphertext, cbCiphertext );

// cleanup:
//     SymCryptWipeKnownSize( pbm, sizeof(pbm) );

//     return scError;
// }

// ERROR
// CALL
// SymCryptMlKemDecapsulate(
//     _In_                                    PCMLKEMKEY pkMlKemkey,
//     _In_reads_bytes_( cbCiphertext )        PCBYTE              pbCiphertext,
//                                             SIZE_T              cbCiphertext,
//     _Out_writes_bytes_( cbAgreedSecret )    PBYTE               pbAgreedSecret,
//                                             SIZE_T              cbAgreedSecret )
// {
//     PINTERNAL_COMPUTATION_TEMPORARIES pCompTemps = NULL;
//     BYTE pbDecryptedRandom[SIZEOF_ENCAPS_RANDOM];
//     BYTE pbDecapsulatedSecret[SIZEOF_AGREED_SECRET];
//     BYTE pbImplicitRejectionSecret[SIZEOF_AGREED_SECRET];
//     PBYTE pbReadCiphertext, pbReencapsulatedCiphertext;
//     BOOLEAN successfulReencrypt;

//     PBYTE pbCurr;
//     PBYTE pbAlloc = NULL;
//     const SIZE_T cbAlloc = sizeof(INTERNAL_COMPUTATION_TEMPORARIES) + (2*cbCiphertext);

//     ERROR scError = NO_ERROR;
//     SIZE_T cbU, cbV, cbCopy;
//     PVECTOR pvu;
//     PPOLYELEMENT peTmp0, peTmp1;
//     PPOLYELEMENT_ACCUMULATOR paTmp;
//     PSHAKE256_STATE pShakeState;
//     const UINT32 nRows = pkMlKemkey->params.nRows;
//     const UINT32 nBitsOfU = pkMlKemkey->params.nBitsOfU;
//     const UINT32 nBitsOfV = pkMlKemkey->params.nBitsOfV;
//     const UINT32 cbPolyElement = pkMlKemkey->params.cbPolyElement;
//     const UINT32 cbVector = pkMlKemkey->params.cbVector;

//     // u vector encoded with nBitsOfU * MLWE_POLYNOMIAL_COEFFICIENTS bits per polynomial
//     cbU = nRows * nBitsOfU * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);
//     // v polynomial encoded with nBitsOfV * MLWE_POLYNOMIAL_COEFFICIENTS bits
//     cbV = nBitsOfV * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);

//     if( (cbAgreedSecret != SIZEOF_AGREED_SECRET) ||
//         (cbCiphertext != cbU + cbV) ||
//         !pkMlKemkey->hasPrivateKey )
//     {
//         scError = INVALID_ARGUMENT;
//         goto cleanup;
//     }

//     pbAlloc = SymCryptCallbackAlloc( cbAlloc );
//     if( pbAlloc == NULL )
//     {
//         scError = MEMORY_ALLOCATION_FAILURE;
//         goto cleanup;
//     }
//     pbCurr = pbAlloc;

//     pCompTemps = (PINTERNAL_COMPUTATION_TEMPORARIES) pbCurr;
//     pbCurr += sizeof(INTERNAL_COMPUTATION_TEMPORARIES);

//     pbReadCiphertext = pbCurr;
//     pbCurr += cbCiphertext;

//     pbReencapsulatedCiphertext = pbCurr;
//     pbCurr += cbCiphertext;

//     ASSERT( pbCurr == (pbAlloc + cbAlloc) );

//     // Read the input ciphertext once to local pbReadCiphertext to ensure our view of ciphertext consistent
//     memcpy( pbReadCiphertext, pbCiphertext, cbCiphertext );

//     pvu = SymCryptMlKemVectorCreate( pCompTemps->abVectorBuffer0, cbVector, nRows );
//     ASSERT( pvu != NULL );
//     peTmp0 = SymCryptMlKemPolyElementCreate( pCompTemps->abPolyElementBuffer0, cbPolyElement );
//     ASSERT( peTmp0 != NULL );
//     peTmp1 = SymCryptMlKemPolyElementCreate( pCompTemps->abPolyElementBuffer1, cbPolyElement );
//     ASSERT( peTmp1 != NULL );
//     paTmp = SymCryptMlKemPolyElementAccumulatorCreate( pCompTemps->abPolyElementAccumulatorBuffer, 2*cbPolyElement );
//     ASSERT( paTmp != NULL );

//     // Decode and decompress u
//     scError = SymCryptMlKemVectorDecodeAndDecompress( pbReadCiphertext, cbU, nBitsOfU, pvu );
//     ASSERT( scError == NO_ERROR );

//     // Perform NTT on u
//     SymCryptMlKemVectorNTT( pvu );

//     // peTmp0 = (s o NTT(u)) ./ R
//     SymCryptMlKemVectorMontDotProduct( pkMlKemkey->pvs, pvu, peTmp0, paTmp );

//     // peTmp0 = INTT(s o NTT(u))
//     SymCryptMlKemPolyElementINTTAndMulR( peTmp0 );

//     // Decode and decompress v
//     scError = SymCryptMlKemPolyElementDecodeAndDecompress( pbReadCiphertext+cbU, nBitsOfV, peTmp1 );
//     ASSERT( scError == NO_ERROR );

//     // peTmp0 = w = v - INTT(s o NTT(u))
//     SymCryptMlKemPolyElementSub( peTmp1, peTmp0, peTmp0 );

//     // pbDecryptedRandom = m' = Encoding of w
//     SymCryptMlKemPolyElementCompressAndEncode( peTmp0, 1, pbDecryptedRandom );

//     // Compute:
//     //  pbDecapsulatedSecret = K' = Decapsulated secret (without implicit rejection)
//     //  pbReencapsulatedCiphertext = c' = Ciphertext from re-encapsulating decrypted random value
//     scError = SymCryptMlKemEncapsulateInternal(
//         pkMlKemkey,
//         pbDecapsulatedSecret, sizeof(pbDecapsulatedSecret),
//         pbReencapsulatedCiphertext, cbCiphertext,
//         pbDecryptedRandom,
//         pCompTemps );
//     ASSERT( scError == NO_ERROR );

//     // Compute the secret we will return if using implicit rejection
//     // pbImplicitRejectionSecret = K_bar = SHAKE256( z || c )
//     pShakeState = &pCompTemps->hashState0.shake256State;
//     SymCryptShake256Init( pShakeState );
//     SymCryptShake256Append( pShakeState, pkMlKemkey->privateRandom, sizeof(pkMlKemkey->privateRandom) );
//     SymCryptShake256Append( pShakeState, pbReadCiphertext, cbCiphertext );
//     SymCryptShake256Extract( pShakeState, pbImplicitRejectionSecret, sizeof(pbImplicitRejectionSecret), FALSE );

//     // Constant time test if re-encryption successful
//     successfulReencrypt = SymCryptEqual( pbReencapsulatedCiphertext, pbReadCiphertext, cbCiphertext );

//     // If not successful, perform side-channel-safe copy of Implicit Rejection secret over Decapsulated secret
//     cbCopy = (((SIZE_T)successfulReencrypt)-1) & SIZEOF_AGREED_SECRET;
//     SymCryptScsCopy( pbImplicitRejectionSecret, cbCopy, pbDecapsulatedSecret, SIZEOF_AGREED_SECRET );

//     // Write agreed secret (with implicit rejection) to pbAgreedSecret
//     memcpy( pbAgreedSecret, pbDecapsulatedSecret, SIZEOF_AGREED_SECRET );

// cleanup:
//     if( pbAlloc != NULL )
//     {
//         SymCryptWipe( pbAlloc, cbAlloc );
//         SymCryptCallbackFree( pbAlloc );
//     }

//     SymCryptWipeKnownSize( pbDecryptedRandom, sizeof(pbDecryptedRandom) );
//     SymCryptWipeKnownSize( pbDecapsulatedSecret, sizeof(pbDecapsulatedSecret) );
//     SymCryptWipeKnownSize( pbImplicitRejectionSecret, sizeof(pbImplicitRejectionSecret) );

//     return scError;
// }
