//
// mlkem.c   ML-KEM related functionality
//
// Copyright (c) Microsoft Corporation. Licensed under the MIT license.
//

use crate::ntt::*;
use crate::key::*;


// TODO: there is no free function, but it would presumably be needed by C callers -- can we figure
// something out, e.g. manually calling the drop trait for a box?

// #define SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(_nRows)   (384UL * _nRows)

// // d and z are each 32 bytes
// #define SIZEOF_FORMAT_PRIVATE_SEED               (2*32)
// // s and t are encoded uncompressed vectors
// // public seed, H(encapsulation key) and z are each 32 bytes
// #define SIZEOF_FORMAT_DECAPSULATION_KEY(_nRows)  ((2*SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(_nRows)) + (3*32))
// // t is encoded uncompressed vector
// // public seed is 32 bytes
// #define SIZEOF_FORMAT_ENCAPSULATION_KEY(_nRows)  (SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(_nRows) + 32)

// ERROR
// CALL
// SymCryptMlKemSizeofKeyFormatFromParams(
//             PARAMS       params,
//             MLKEMKEY_FORMAT    mlKemkeyFormat,
//     _Out_   SIZE_T*                     pcbKeyFormat )
// {
//     ERROR scError = NO_ERROR;
//     INTERNAL_PARAMS internalParams;

//     if( mlKemkeyFormat == MLKEMKEY_FORMAT_NULL )
//     {
//         scError = INCOMPATIBLE_FORMAT;
//         goto cleanup;
//     }

//     scError = SymCryptMlKemkeyGetInternalParamsFromParams(params, &internalParams);
//     if( scError != NO_ERROR )
//     {
//         goto cleanup;
//     }

//     switch( mlKemkeyFormat )
//     {
//         case MLKEMKEY_FORMAT_PRIVATE_SEED:
//             *pcbKeyFormat = SIZEOF_FORMAT_PRIVATE_SEED;
//             break;

//         case MLKEMKEY_FORMAT_DECAPSULATION_KEY:
//             *pcbKeyFormat = SIZEOF_FORMAT_DECAPSULATION_KEY(internalParams.nRows);
//             break;

//         case MLKEMKEY_FORMAT_ENCAPSULATION_KEY:
//             *pcbKeyFormat = SIZEOF_FORMAT_ENCAPSULATION_KEY(internalParams.nRows);
//             break;

//         default:
//             scError = INVALID_ARGUMENT;
//             goto cleanup;
//     }

// cleanup:
//     return scError;
// }

// ERROR
// CALL
// SymCryptMlKemSizeofCiphertextFromParams(
//             PARAMS       params,
//     _Out_   SIZE_T*                     pcbCiphertext )
// {
//     ERROR scError = NO_ERROR;
//     INTERNAL_PARAMS internalParams;
//     SIZE_T cbU, cbV;

//     scError = SymCryptMlKemkeyGetInternalParamsFromParams(params, &internalParams);
//     if( scError != NO_ERROR )
//     {
//         goto cleanup;
//     }

//     // u vector encoded with nBitsOfU * MLWE_POLYNOMIAL_COEFFICIENTS bits per polynomial
//     cbU = ((SIZE_T)internalParams.nRows) * internalParams.nBitsOfU * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);
//     // v polynomial encoded with nBitsOfV * MLWE_POLYNOMIAL_COEFFICIENTS bits
//     cbV = ((SIZE_T)internalParams.nBitsOfV) * (MLWE_POLYNOMIAL_COEFFICIENTS / 8);
//     *pcbCiphertext = cbU + cbV;

//     ASSERT( (internalParams.params != PARAMS_MLKEM512)  || ((cbU + cbV) == CIPHERTEXT_SIZE_MLKEM512)  );
//     ASSERT( (internalParams.params != PARAMS_MLKEM768)  || ((cbU + cbV) == CIPHERTEXT_SIZE_MLKEM768)  );
//     ASSERT( (internalParams.params != PARAMS_MLKEM1024) || ((cbU + cbV) == CIPHERTEXT_SIZE_MLKEM1024) );

// cleanup:
//     return scError;
// }

// static
// VOID
// CALL
// SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed(
//     _Inout_ PMLKEMKEY                                  pkMlKemkey,
//     _Inout_ PINTERNAL_COMPUTATION_TEMPORARIES    pCompTemps )
// {
//     UINT32 i, j;
//     BYTE coordinates[2];

//     PSHAKE128_STATE pShakeStateBase = &pCompTemps->hashState0.shake128State;
//     PSHAKE128_STATE pShakeStateWork = &pCompTemps->hashState1.shake128State;
//     const UINT32 nRows = pkMlKemkey->params.nRows;

//     SymCryptShake128Init( pShakeStateBase );
//     SymCryptShake128Append( pShakeStateBase, pkMlKemkey->publicSeed, sizeof(pkMlKemkey->publicSeed) );

//     for( i=0; i<nRows; i++ )
//     {
//         coordinates[1] = (BYTE)i;
//         for( j=0; j<nRows; j++ )
//         {
//             coordinates[0] = (BYTE)j;
//             SymCryptShake128StateCopy( pShakeStateBase, pShakeStateWork );
//             SymCryptShake128Append( pShakeStateWork, coordinates, sizeof(coordinates) );

//             SymCryptMlKemPolyElementSampleNTTFromShake128( pShakeStateWork, pkMlKemkey->pmAtranspose->apPolyElements[(i*nRows)+j] );
//         }
//     }

//     // no need to wipe; everything computed here is always public
// }

// static
// VOID
// CALL
// SymCryptMlKemkeyComputeEncapsulationKeyHash(
//     _Inout_ PMLKEMKEY                                  pkMlKemkey,
//     _Inout_ PINTERNAL_COMPUTATION_TEMPORARIES    pCompTemps,
//             SIZE_T                                              cbEncodedVector )
// {
//     PSHA3_256_STATE pState = &pCompTemps->hashState0.sha3_256State;

//     SymCryptSha3_256Init( pState );
//     SymCryptSha3_256Append( pState, pkMlKemkey->encodedT, cbEncodedVector );
//     SymCryptSha3_256Append( pState, pkMlKemkey->publicSeed, sizeof(pkMlKemkey->publicSeed) );
//     SymCryptSha3_256Result( pState, pkMlKemkey->encapsKeyHash );
// }

// static
// VOID
// CALL
// SymCryptMlKemkeyExpandFromPrivateSeed(
//     _Inout_ PMLKEMKEY                                  pkMlKemkey,
//     _Inout_ PINTERNAL_COMPUTATION_TEMPORARIES    pCompTemps )
// {
//     BYTE privateSeedHash[SHA3_512_RESULT_SIZE];
//     BYTE CBDSampleBuffer[3*64 + 1];
//     PVECTOR pvTmp;
//     PPOLYELEMENT_ACCUMULATOR paTmp;
//     PSHAKE256_STATE pShakeStateBase = &pCompTemps->hashState0.shake256State;
//     PSHAKE256_STATE pShakeStateWork = &pCompTemps->hashState1.shake256State;
//     UINT32 i;
//     const UINT32 nRows = pkMlKemkey->params.nRows;
//     const UINT32 nEta1 = pkMlKemkey->params.nEta1;
//     const SIZE_T cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR(nRows);
//     const UINT32 cbPolyElement = pkMlKemkey->params.cbPolyElement;
//     const UINT32 cbVector = pkMlKemkey->params.cbVector;

//     ASSERT( pkMlKemkey->hasPrivateSeed );
//     ASSERT( (nEta1 == 2) || (nEta1 == 3) );
//     ASSERT( cbEncodedVector <= sizeof(pkMlKemkey->encodedT) );

//     pvTmp = SymCryptMlKemVectorCreate( pCompTemps->abVectorBuffer0, cbVector, nRows );
//     ASSERT( pvTmp != NULL );
//     paTmp = SymCryptMlKemPolyElementAccumulatorCreate( pCompTemps->abPolyElementAccumulatorBuffer, 2*cbPolyElement );
//     ASSERT( paTmp != NULL );

//     // (rho || sigma) = G(d || k)
//     // use CBDSampleBuffer to concatenate the private seed and encoding of nRows
//     memcpy( CBDSampleBuffer, pkMlKemkey->privateSeed, sizeof(pkMlKemkey->privateSeed) );
//     CBDSampleBuffer[sizeof(pkMlKemkey->privateSeed)] = (BYTE) nRows;
//     SymCryptSha3_512( CBDSampleBuffer, sizeof(pkMlKemkey->privateSeed)+1, privateSeedHash );

//     // copy public seed
//     memcpy( pkMlKemkey->publicSeed, privateSeedHash, sizeof(pkMlKemkey->publicSeed) );

//     // generate A from public seed
//     SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed( pkMlKemkey, pCompTemps );

//     // Initialize pShakeStateBase with sigma
//     SymCryptShake256Init( pShakeStateBase );
//     SymCryptShake256Append( pShakeStateBase, privateSeedHash+sizeof(pkMlKemkey->publicSeed), 32 );

//     // Expand s in place
//     for( i=0; i<nRows; i++ )
//     {
//         CBDSampleBuffer[0] = (BYTE) i;
//         SymCryptShake256StateCopy( pShakeStateBase, pShakeStateWork );
//         SymCryptShake256Append( pShakeStateWork, CBDSampleBuffer, 1 );

//         SymCryptShake256Extract( pShakeStateWork, CBDSampleBuffer, 64ul*nEta1, FALSE );

//         SymCryptMlKemPolyElementSampleCBDFromBytes( CBDSampleBuffer, nEta1, INTERNAL_MLKEM_VECTOR_ELEMENT(i, pkMlKemkey->pvs) );
//     }
//     // Expand e in t, ready for multiply-add
//     for( i=0; i<nRows; i++ )
//     {
//         CBDSampleBuffer[0] = (BYTE) (nRows+i);
//         SymCryptShake256StateCopy( pShakeStateBase, pShakeStateWork );
//         SymCryptShake256Append( pShakeStateWork, CBDSampleBuffer, 1 );

//         SymCryptShake256Extract( pShakeStateWork, CBDSampleBuffer, 64ul*nEta1, FALSE );

//         SymCryptMlKemPolyElementSampleCBDFromBytes( CBDSampleBuffer, nEta1, INTERNAL_MLKEM_VECTOR_ELEMENT(i, pkMlKemkey->pvt) );
//     }

//     // Perform NTT on s and e
//     SymCryptMlKemVectorNTT( pkMlKemkey->pvs );
//     SymCryptMlKemVectorNTT( pkMlKemkey->pvt );

//     // pvTmp = s .* R
//     SymCryptMlKemVectorMulR( pkMlKemkey->pvs, pvTmp );

//     // t = ((A o (s .* R)) ./ R) + e = A o s + e
//     SymCryptMlKemMatrixVectorMontMulAndAdd( pkMlKemkey->pmAtranspose, pvTmp, pkMlKemkey->pvt, paTmp );

//     // transpose A
//     SymCryptMlKemMatrixTranspose( pkMlKemkey->pmAtranspose );

//     // precompute byte-encoding of public vector t
//     SymCryptMlKemVectorCompressAndEncode( pkMlKemkey->pvt, 12, pkMlKemkey->encodedT, cbEncodedVector );

//     // precompute hash of encapsulation key blob
//     SymCryptMlKemkeyComputeEncapsulationKeyHash( pkMlKemkey, pCompTemps, cbEncodedVector );

//     // Cleanup!
//     SymCryptWipeKnownSize( privateSeedHash, sizeof(privateSeedHash) );
//     SymCryptWipeKnownSize( CBDSampleBuffer, sizeof(CBDSampleBuffer) );
// }

// ERROR
// CALL
// SymCryptMlKemkeySetValue(
//     _In_reads_bytes_( cbSrc )   PCBYTE                      pbSrc,
//                                 SIZE_T                      cbSrc,
//                                 MLKEMKEY_FORMAT    mlKemkeyFormat,
//                                 UINT32                      flags,
//     _Inout_                     PMLKEMKEY          pkMlKemkey )
// {
//     ERROR scError = NO_ERROR;
//     PCBYTE pbCurr = pbSrc;
//     PINTERNAL_COMPUTATION_TEMPORARIES pCompTemps = NULL;
//     const UINT32 nRows = pkMlKemkey->params.nRows;
//     const SIZE_T cbEncodedVector = SIZEOF_ENCODED_UNCOMPRESSED_VECTOR( nRows );

//     // Ensure only allowed flags are specified
//     UINT32 allowedFlags = FLAG_KEY_NO_FIPS | FLAG_KEY_MINIMAL_VALIDATION;

//     if ( ( flags & ~allowedFlags ) != 0 )
//     {
//         scError = INVALID_ARGUMENT;
//         goto cleanup;
//     }

//     // Check that minimal validation flag only specified with no fips
//     if ( ( ( flags & FLAG_KEY_NO_FIPS ) == 0 ) &&
//          ( ( flags & FLAG_KEY_MINIMAL_VALIDATION ) != 0 ) )
//     {
//         scError = INVALID_ARGUMENT;
//         goto cleanup;
//     }

//     if( mlKemkeyFormat == MLKEMKEY_FORMAT_NULL )
//     {
//         scError = INVALID_ARGUMENT;
//         goto cleanup;
//     }

//     if( ( flags & FLAG_KEY_NO_FIPS ) == 0 )
//     {
//         // Ensure ML-KEM algorithm selftest is run before first use of ML-KEM algorithms;
//         // notably _before_ first full KeyGen
//         RUN_SELFTEST_ONCE(
//             SymCryptMlKemSelftest,
//             SELFTEST_ALGORITHM_MLKEM);
//     }

//     pCompTemps = SymCryptCallbackAlloc( sizeof(INTERNAL_COMPUTATION_TEMPORARIES) );
//     if( pCompTemps == NULL )
//     {
//         scError = MEMORY_ALLOCATION_FAILURE;
//         goto cleanup;
//     }

//     if( mlKemkeyFormat == MLKEMKEY_FORMAT_PRIVATE_SEED )
//     {
//         if( cbSrc != SIZEOF_FORMAT_PRIVATE_SEED )
//         {
//             scError = WRONG_KEY_SIZE;
//             goto cleanup;
//         }

//         pkMlKemkey->hasPrivateSeed = TRUE;
//         memcpy( pkMlKemkey->privateSeed, pbCurr, sizeof(pkMlKemkey->privateSeed) );
//         pbCurr += sizeof(pkMlKemkey->privateSeed);

//         pkMlKemkey->hasPrivateKey = TRUE;
//         memcpy( pkMlKemkey->privateRandom, pbCurr, sizeof(pkMlKemkey->privateRandom) );
//         pbCurr += sizeof(pkMlKemkey->privateRandom);

//         SymCryptMlKemkeyExpandFromPrivateSeed( pkMlKemkey, pCompTemps );
//     }
//     else if( mlKemkeyFormat == MLKEMKEY_FORMAT_DECAPSULATION_KEY )
//     {
//         if( cbSrc != SIZEOF_FORMAT_DECAPSULATION_KEY( nRows ) )
//         {
//             scError = WRONG_KEY_SIZE;
//             goto cleanup;
//         }

//         // decode s
//         scError = SymCryptMlKemVectorDecodeAndDecompress( pbCurr, cbEncodedVector, 12, pkMlKemkey->pvs );
//         if( scError != NO_ERROR )
//         {
//             goto cleanup;
//         }
//         pbCurr += cbEncodedVector;

//         // copy t and decode t
//         memcpy( pkMlKemkey->encodedT, pbCurr, cbEncodedVector );
//         pbCurr += cbEncodedVector;
//         scError = SymCryptMlKemVectorDecodeAndDecompress( pkMlKemkey->encodedT, cbEncodedVector, 12, pkMlKemkey->pvt );
//         if( scError != NO_ERROR )
//         {
//             goto cleanup;
//         }

//         // copy public seed and expand public matrix
//         memcpy( pkMlKemkey->publicSeed, pbCurr, sizeof(pkMlKemkey->publicSeed) );
//         pbCurr += sizeof(pkMlKemkey->publicSeed);
//         SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed( pkMlKemkey, pCompTemps );

//         // transpose A
//         SymCryptMlKemMatrixTranspose( pkMlKemkey->pmAtranspose );

//         // copy hash of encapsulation key
//         memcpy( pkMlKemkey->encapsKeyHash, pbCurr, sizeof(pkMlKemkey->encapsKeyHash) );
//         pbCurr += sizeof(pkMlKemkey->encapsKeyHash);

//         // copy private random
//         memcpy( pkMlKemkey->privateRandom, pbCurr, sizeof(pkMlKemkey->privateRandom) );
//         pbCurr += sizeof(pkMlKemkey->privateRandom);

//         pkMlKemkey->hasPrivateSeed = FALSE;
//         pkMlKemkey->hasPrivateKey  = TRUE;
//     }
//     else if( mlKemkeyFormat == MLKEMKEY_FORMAT_ENCAPSULATION_KEY )
//     {
//         if( cbSrc != SIZEOF_FORMAT_ENCAPSULATION_KEY( nRows ) )
//         {
//             scError = WRONG_KEY_SIZE;
//             goto cleanup;
//         }

//         // copy t and decode t
//         memcpy( pkMlKemkey->encodedT, pbCurr, cbEncodedVector );
//         pbCurr += cbEncodedVector;
//         scError = SymCryptMlKemVectorDecodeAndDecompress( pkMlKemkey->encodedT, cbEncodedVector, 12, pkMlKemkey->pvt );
//         if( scError != NO_ERROR )
//         {
//             goto cleanup;
//         }

//         // copy public seed and expand public matrix
//         memcpy( pkMlKemkey->publicSeed, pbCurr, sizeof(pkMlKemkey->publicSeed) );
//         pbCurr += sizeof(pkMlKemkey->publicSeed);
//         SymCryptMlKemkeyExpandPublicMatrixFromPublicSeed( pkMlKemkey, pCompTemps );

//         // transpose A
//         SymCryptMlKemMatrixTranspose( pkMlKemkey->pmAtranspose );

//         // precompute hash of encapsulation key blob
//         SymCryptMlKemkeyComputeEncapsulationKeyHash( pkMlKemkey, pCompTemps, cbEncodedVector );

//         pkMlKemkey->hasPrivateSeed = FALSE;
//         pkMlKemkey->hasPrivateKey  = FALSE;
//     }
//     else
//     {
//         scError = NOT_IMPLEMENTED;
//         goto cleanup;
//     }

//     ASSERT( pbCurr == pbSrc + cbSrc );

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
