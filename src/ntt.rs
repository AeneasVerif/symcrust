//
// ntt.rs: a minimal NTT taken from SymCrypt, rewritten in Rust, to be verified with Aeneas and
// extracted to C with Eurydice
//
// Copyright (c) Microsoft Corporation. Licensed under the MIT license.
//

// Internal ML-KEM definitions for the symcrypt library.
// Always intended to be included as part of sc_lib.h
//

//
// ML-KEM (also known as Kyber) and ML-DSA (also known as Dilithium) are Post-Quantum algorithms based on the
// Learning-With-Errors problem over Module Lattices (or the hardness of the M-LWE problem).
//
// A Module is a Vector Space over a Ring. That is, elements of the vector spaces are elements in the
// underlying ring.
// We refer to Module as MLWE in the below types to avoid naming confusion with Module as in "FIPS module".
// Though technically components acting on MLWE types could be used outside of the MLWE problem, these types
// are SymCrypt-internal, and are only currently intended for use in these MLWE-based algorithms.
//
// In ML-KEM and ML-DSA, Polynomial Rings are used. That is, a ring defined over polynomials.
// For both schemes, the polynomial ring is defined modulo the polynomial (X^256 + 1). This means there is a
// representative of each polynomial ring element with 256 coefficients (c_255*X^255 + c_254*X^254 + ... + c_0).
// The coefficients themselves are modulo a small prime in both schemes. For ML-KEM the small prime is 3329
// (12-bits), and for ML-DSA the small prime is 8380417 (23-bits).
// Additionally, for both schemes there is a Number Theoretic Transform (NTT) which maps polynomial ring elements
// to a corresponding ring for efficient multiplication.
// The in-memory representation of a polynomial ring element uses the same struct regardless of whether it is in
// standard form, or the NTT form. For brevity we tend to refer to polynomial ring elements as PolyElements.
//

#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]

// FIXME: using a range-based iterator involves a remarkable amount of traits, including advanced
// features like associated types; for the quality of the C code, we instead rely on a custom macro
// that expands to a while-loop, to be later peephole-optimized into a C for loop

macro_rules! c_for {
    ($decl:stmt; $test:expr; $incr:expr; $body:block) => {
        $decl
        while ($test) {
            $body;
            $incr
        }
    }
}


const MLWE_POLYNOMIAL_COEFFICIENTS: usize = 256;

//=====================================================
//  ML-KEM internal high level types
//

// PolyElements just store the coefficients without any header.
type POLYELEMENT = [u16; MLWE_POLYNOMIAL_COEFFICIENTS ];

type POLYELEMENT_ACCUMULATOR = [u32; MLWE_POLYNOMIAL_COEFFICIENTS ];

// Currently maximum size of MLKEM matrices is baked in, they are always square and up to 4x4.
const MATRIX_MAX_NROWS: usize = 4;

// The slice length is between 1 and MATRIX_MAX_NROWS.
// Note (Rust): unlike the original C code, we de-couple what we pass around (this type) vs. the
// underlying allocation (handled by the caller).
// Note (Rust): this already keeps the length -- no need for an additional field.
type VECTOR = [POLYELEMENT];

// Array of pointers to PolyElements in row-major order
// Note: the extra indirection is intentional to make transposing the matrix cheap,
// given that in the MLKEM context the underlying PolyElements are relatively large
// so we don't want to move them around.
//
// Note (Rust): this will work because the thing has a fixed size and so we can declare 16
// variables in scope, borrow them all, and put them in an array (or use split_at_mut).
//
// Note (Rust): again, allocation to be handled by the caller or the owner.
// Note (Rust): to avoid a const-generic, the array of pointers to elements is possibly oversized
struct MATRIX<'a> {
    nRows: usize,
    apPolyElements: [&'a mut POLYELEMENT; MATRIX_MAX_NROWS * MATRIX_MAX_NROWS],
}

//
// MLKEMKEY type
//

const KEY_MAX_SIZEOF_ENCODED_T: usize = 1536;

struct INTERNAL_PARAMS {
    params: u32,         // parameter set of ML-KEM being used, takes a value from PARAMS

    cbPolyElement: u32,  // size of one polynomial ring element
    cbVector: u32,       // size of one vector
    cbMatrix: u32,       // size of one matrix

    nRows: u8,           // corresponds to k from FIPS 203; the number of rows and columns in the matrix A,
                         // and the number of rows in column vectors s and t
    nEta1: u8,           // corresponds to eta_1 from FIPS 203; number of coinflips used in generating s and e
                         // in keypair generation, and r in encapsulation
    nEta2: u8,           // corresponds to eta_2 from FIPS 203; number of coinflips used in generating e_1 and
                         // e_2 in encapsulation
    nBitsOfU: u8,        // corresponds to d_u from FIPS 203; number of bits that the coefficients of the polynomial
                         // ring elements of u are compressed to in encapsulation for encoding into ciphertext
    nBitsOfV: u8,        // corresponds to d_v from FIPS 203; number of bits that the coefficients of the polynomial
                         // ring element v is compressed to in encapsulation for encoding into ciphertext
}

struct KEY<'a> {
    fAlgorithmInfo: u32, // Tracks which algorithms the key can be used in
                                            // Also tracks which per-key selftests have been performed on this key
                                            // A bitwise OR of FLAG_KEY_*, FLAG_MLKEMKEY_*, and
                                            // SELFTEST_KEY_* values

    params: INTERNAL_PARAMS,

    cbTotalSize: u32,    // Total in-memory size of the ML-KEM key (this header and the following structs)

    hasPrivateSeed: bool, // Set to true if key has the private seed (d)
    hasPrivateKey: bool,  // Set to true if key has the private key (s and z)

    // seeds
    privateSeed: [u8; 32],    // private seed (d) from which entire private PKE key can be derived
    privateRandom: [u8; 32],  // private random (z) used in implicit rejection

    publicSeed: [u8; 32],     // public seed (rho) from which A can be derived

    // A o s + e = t
    pmAtranspose: MATRIX<'a>,   // public matrix in NTT form (derived from publicSeed)
    pvt: &'a mut VECTOR,        // public vector in NTT form

    pvs: &'a mut VECTOR,        // private vector in NTT form

    // misc fields
    encodedT: [u8; KEY_MAX_SIZEOF_ENCODED_T], // byte-encoding of public vector
                                                                              // may only use a prefix of this buffer
    encapsKeyHash: [u8; 32],  // Precomputed value of hash of ML-KEM's byte-encoding of encapsulation key
}

//=====================================================
//  ML-KEM primitives
//

const Q: u32 = 3329;

// Old constants for C-style header + allocation
// #define INTERNAL_MLKEM_SIZEOF_POLYRINGELEMENT              ( sizeof(POLYELEMENT) )
// #define INTERNAL_MLKEM_SIZEOF_POLYRINGELEMENT_ACCUMULATOR  ( sizeof(POLYELEMENT_ACCUMULATOR) )
// #define INTERNAL_MLKEM_MAXIMUM_VECTOR_SIZE                 ( sizeof(VECTOR) + (MATRIX_MAX_NROWS * INTERNAL_MLKEM_SIZEOF_POLYRINGELEMENT) )
// #define INTERNAL_MLKEM_VECTOR_ELEMENT_OFFSET( _row )       ( sizeof(VECTOR) + ((_row) * INTERNAL_MLKEM_SIZEOF_POLYRINGELEMENT) )
// #define INTERNAL_MLKEM_VECTOR_ELEMENT( _row, _pVector )    (PPOLYELEMENT)( (PBYTE)(_pVector) + INTERNAL_MLKEM_VECTOR_ELEMENT_OFFSET(_row) )

const SIZEOF_MAX_CIPHERTEXT: usize = 1568;
const SIZEOF_AGREED_SECRET: usize = 32;
const SIZEOF_ENCAPS_RANDOM: usize = 32;

// FIXME
type shake128State = [u8; 0];
type shake256State = [u8; 0];
type sha3_256State = [u8; 0];
type sha3_512State = [u8; 0];

// TODO:
/*union HashStateUnion {
    shake128State: shake128State,
    shake256State: shake256State,
    sha3_256State: sha3_256State,
    sha3_512State: sha3_512State,
}*/

// Note (Rust): caller allocates these temporaries whichever way they want, and passes us a mutable
// reference to such a struct. If we need to use several fields at once, we can use a `ref mut`
// pattern in Rust.
struct INTERNAL_COMPUTATION_TEMPORARIES {
    abVectorBuffer0: [POLYELEMENT; MATRIX_MAX_NROWS],
    abVectorBuffer1: [POLYELEMENT; MATRIX_MAX_NROWS],
    abPolyElementBuffer0: POLYELEMENT,
    abPolyElementBuffer1: POLYELEMENT,
    abPolyElementAccumulatorBuffer: POLYELEMENT_ACCUMULATOR,
    //hashState0: HashStateUnion, // TODO
    //hashState1: HashStateUnion, // TODO
}


//
// ML-KEM operations acting on individual polynomial ring elements (PolyElements)
//

//
// See ML-KEM Polynomial Ring Element Decode and Decompress
//
//
// Current approach is to represent polynomial ring elements as a 512-byte buffer (256 UINT16s).
//

// Coefficients are added and subtracted when polynomials are in the NTT domain and in the lattice domain.
//
// Coefficients are only multiplied in the NTT/INTT operations, and in MulAdd which only operates on
// polynomials in NTT form.
// We choose to perform modular multiplication exclusively using Montgomery multiplication, that is, we choose
// a Montgomery divisor R, and modular multiplication always divides by R, as this make reduction logic easy
// and quick.
// i.e. MontMul(a,b) -> ((a*b) / R) mod Q
//
// For powers of Zeta used in as multiplication twiddle factors in NTT/INTT and base polynomial multiplication,
// we pre-multiply the constants by R s.t.
//  MontMul(x, twiddleForZetaToTheK) -> x*(Zeta^K) mod Q.
//
// Most other modular multiplication can be done with a fixup deferred until the INTT. The one exception is in key
// generation, where A o s + e = t, we need to pre-multiply s'

// R = 2^16
const Rlog2: u32 = 16;
const Rmask: u32 = 0xffff;

// NegQInvModR = -Q^(-1) mod R
const NegQInvModR: u32 = 3327;

// Rsqr = R^2 = (1<<32) mod Q
const Rsqr: u32 = 1353;
// RsqrTimesNegQInvModR = R^2 = ((1<<32) mod Q) * -Q^(-1) mod R
const RsqrTimesNegQInvModR: u32 = 44983;

//
// Zeta tables.
// Zeta = 17, which is a primitive 256-th root of unity modulo Q
//
// In ML-KEM we use powers of zeta to convert to and from NTT form
// and to perform multiplication between polynomials in NTT form
//

// This table is a lookup for (Zeta^(BitRev(index)) * R) mod Q
// Used in NTT and INTT
// i.e. element 1 is Zeta^(BitRev(1)) * (2^16) mod Q == (17^64)*(2^16) mod 3329 == 2571
//
// MlKemZetaBitRevTimesR = [ (pow(17, bitRev(i)) << 16) % 3329 for i in range(128) ]
const MlKemZetaBitRevTimesR: [u16; 128] = [
    2285, 2571, 2970, 1812, 1493, 1422,  287,  202,
    3158,  622, 1577,  182,  962, 2127, 1855, 1468,
     573, 2004,  264,  383, 2500, 1458, 1727, 3199,
    2648, 1017,  732,  608, 1787,  411, 3124, 1758,
    1223,  652, 2777, 1015, 2036, 1491, 3047, 1785,
     516, 3321, 3009, 2663, 1711, 2167,  126, 1469,
    2476, 3239, 3058,  830,  107, 1908, 3082, 2378,
    2931,  961, 1821, 2604,  448, 2264,  677, 2054,
    2226,  430,  555,  843, 2078,  871, 1550,  105,
     422,  587,  177, 3094, 3038, 2869, 1574, 1653,
    3083,  778, 1159, 3182, 2552, 1483, 2727, 1119,
    1739,  644, 2457,  349,  418,  329, 3173, 3254,
     817, 1097,  603,  610, 1322, 2044, 1864,  384,
    2114, 3193, 1218, 1994, 2455,  220, 2142, 1670,
    2144, 1799, 2051,  794, 1819, 2475, 2459,  478,
    3221, 3021,  996,  991,  958, 1869, 1522, 1628,
];

// This table is a lookup for ((Zeta^(BitRev(index)) * R) mod Q) * -Q^(-1) mod R
// Used in NTT and INTT
//
// MlKemZetaBitRevTimesRTimesNegQInvModR = [ (((pow(17, bitRev(i)) << 16) % Q) * 3327) & 0xffff for i in range(128) ]
const MlKemZetaBitRevTimesRTimesNegQInvModR: [u16; 128] = [
       19, 34037, 50790, 64748, 52011, 12402, 37345, 16694,
    20906, 37778,  3799, 15690, 54846, 64177, 11201, 34372,
     5827, 48172, 26360, 29057, 59964,  1102, 44097, 26241,
    28072, 41223, 10532, 56736, 47109, 56677, 38860, 16162,
     5689,  6516, 64039, 34569, 23564, 45357, 44825, 40455,
    12796, 38919, 49471, 12441, 56401,   649, 25986, 37699,
    45652, 28249, 15886,  8898, 28309, 56460, 30198, 47286,
    52109, 51519, 29155, 12756, 48704, 61224, 24155, 17914,
      334, 54354, 11477, 52149, 32226, 14233, 45042, 21655,
    27738, 52405, 64591,  4586, 14882, 42443, 59354, 60043,
    33525, 32502, 54905, 35218, 36360, 18741, 28761, 52897,
    18485, 45436, 47975, 47011, 14430, 46007,  5275, 12618,
    31183, 45239, 40101, 63390,  7382, 50180, 41144, 32384,
    20926,  6279, 54590, 14902, 41321, 11044, 48546, 51066,
    55200, 21497,  7933, 20198, 22501, 42325, 54629, 17442,
    33899, 23859, 36892, 20257, 41538, 57779, 17422, 42404,
];

// This table is a lookup for ((Zeta^(2*BitRev(index) + 1) * R) mod Q)
// Used in multiplication of 2 NTT-form polynomials
//
// zetaTwoTimesBitRevPlus1TimesR =  [ (pow(17, 2*bitRev(i)+1) << 16) % 3329 for i in range(128) ]
const zetaTwoTimesBitRevPlus1TimesR: [u16; 128] = [
    2226, 1103,  430, 2899,  555, 2774,  843, 2486,
    2078, 1251,  871, 2458, 1550, 1779,  105, 3224,
     422, 2907,  587, 2742,  177, 3152, 3094,  235,
    3038,  291, 2869,  460, 1574, 1755, 1653, 1676,
    3083,  246,  778, 2551, 1159, 2170, 3182,  147,
    2552,  777, 1483, 1846, 2727,  602, 1119, 2210,
    1739, 1590,  644, 2685, 2457,  872,  349, 2980,
     418, 2911,  329, 3000, 3173,  156, 3254,   75,
     817, 2512, 1097, 2232,  603, 2726,  610, 2719,
    1322, 2007, 2044, 1285, 1864, 1465,  384, 2945,
    2114, 1215, 3193,  136, 1218, 2111, 1994, 1335,
    2455,  874,  220, 3109, 2142, 1187, 1670, 1659,
    2144, 1185, 1799, 1530, 2051, 1278,  794, 2535,
    1819, 1510, 2475,  854, 2459,  870,  478, 2851,
    3221,  108, 3021,  308,  996, 2333,  991, 2338,
     958, 2371, 1869, 1460, 1522, 1807, 1628, 1701,
];


fn SymCryptMlKemModAdd(a: u32, b: u32) -> u32 {
    assert!( a < Q );
    assert!( b < Q );

    // In the comments below, we manipulate unbounded integers.
    // res = (a + b) - Q
    let res = (a + b).wrapping_sub(Q); // -Q <= res < Q
    assert!( ((res >> 16) == 0) || ((res >> 16) == 0xffff) );
    // If res < 0, then: Q & (res >> 16) = Q
    // Otherwise: Q & (res >> 16) = 0
    let res = res.wrapping_add(Q & (res >> 16));
    assert!( res < Q );

    return res;
}

fn SymCryptMlKemModSub(a: u32, b: u32) -> u32 {
    // This function is called in two situations:
    // - when we want to substract to field elements which are < Q
    // - when we performed an addition and want to substract Q so
    //   that the result is < Q
    assert!( a < 2*Q );
    assert!( b <= Q );

    // In the comments below, we manipulate unbounded integers.
    // res = a - b
    let res = a.wrapping_sub(b); // -Q <= res < 2 * Q
    assert!( ((res >> 16) == 0) || ((res >> 16) == 0xffff) );
    // If res < 0, then: Q & (res >> 16) = Q
    // Otherwise: Q & (res >> 16) = 0
    let res = res.wrapping_add(Q & (res >> 16));
    // 0 <= res < 2 * Q
    assert!( res < Q ); // SH: how do we justify this given the bound: a < 2*Q?
    // SH: I believe it depends on the situation: we may have to prove several
    // auxiliary lemmas for this (there are situations where we call this function
    // with a < Q for instance).

    return res;
}

/// Computes: ((a * b) / R) % Q
///
/// This simply applies the montgomery reduction to: a * b
///
/// Pre:
///  bMont = (b * NegQInvModR) % R
///  bMont <= R
fn SymCryptMlKemMontMul(a: u32, b: u32, bMont: u32) -> u32 {
    assert!( a < Q );
    assert!( b < Q );
    assert!( bMont <= Rmask );
    assert!( bMont == ((b * NegQInvModR) & Rmask) );

    let mut res = a * b;
    let inv = (a * bMont) & Rmask;
    res += inv * Q;
    //assert!( (res & Rmask) == 0 );
    res = res >> Rlog2;

    // By doing this we always get back within the bounds
    return SymCryptMlKemModSub( res, Q );
}

fn SymCryptMlKemPolyElementNTTLayerC(peSrc: &mut POLYELEMENT, mut k: usize, len: usize) {
    // FIXME (see comments in eurydice/lib/Builtin.ml)
    // WAS: for start in (0usize..256).step_by(2*len) {
    c_for!(let mut start = 0usize; start < 256; start += 2*len; {
        let twiddleFactor: u32 = MlKemZetaBitRevTimesR[k].into();
        // twiddleFactor = (Zeta^BitRev(k) * R) mod Q
        let twiddleFactorMont: u32 = MlKemZetaBitRevTimesRTimesNegQInvModR[k].into();
        // twiddleFactorMont = (((Zeta^BitRev(k) * R) mod Q) * -Q^(-1) mod R)
        k += 1;

        #[inline]
        fn inner_loop(peSrc: &mut POLYELEMENT, len: usize,
                      start: usize, twiddleFactor: u32, twiddleFactorMont: u32) {
            c_for!(let mut j = 0usize; j < len; j += 1; {
                let mut c0: u32 = peSrc[start+j].into();
                // c0 = f(start + j);
                assert!( c0 < Q );
                let mut c1: u32 = peSrc[start+j+len].into();
                // c1 = f(start + j + len);
                assert!( c1 < Q );

                let c1TimesTwiddle: u32 = SymCryptMlKemMontMul( c1, twiddleFactor, twiddleFactorMont );
                // c1TimesTwiddle = ((c1 * (Zeta^BitRev(k) * R)) / R) % Q
                //                = ((f(start + j + len) * (Zeta^BitRev(k) * R)) / R) mod Q
                //                = (f(start + j + len) * Zeta^BitRev(k)) mod Q

                c1 = SymCryptMlKemModSub( c0, c1TimesTwiddle );
                // c1 = (f(start + j) - f(start + j + len) * Zeta^BitRev(k)) mod Q
                c0 = SymCryptMlKemModAdd( c0, c1TimesTwiddle );
                // c0 = (f(start + j) + f(start + j + len) * Zeta^BitRev(k)) mod Q

                peSrc[start+j]      = c0 as u16;
                peSrc[start+j+len]  = c1 as u16;
            });
        }
        inner_loop(peSrc, len, start, twiddleFactor, twiddleFactorMont);
    });
}

fn SymCryptMlKemPolyElementINTTLayerC(peSrc: &mut POLYELEMENT, mut k: usize, len: usize) {
    // FIXME
    // for start in (0..256).step_by(2*len) {
    c_for!(let mut start = 0usize; start < 256; start += 2*len; {
        let twiddleFactor: u32 = MlKemZetaBitRevTimesR[k].into();
        // twiddleFactor = (Zeta^BitRev(k) * R) mod Q
        let twiddleFactorMont: u32 = MlKemZetaBitRevTimesRTimesNegQInvModR[k].into();
        // twiddleFactorMont = (((Zeta^BitRev(k) * R) mod Q) * -Q^(-1) mod R) mod Q
        k -= 1;

        inner_loop(peSrc, len, start, twiddleFactor, twiddleFactorMont);
        #[inline]
        fn inner_loop(peSrc: &mut POLYELEMENT, len: usize,
                      start: usize, twiddleFactor: u32, twiddleFactorMont: u32) {
            c_for!(let mut j = 0; j < len; j += 1; {
                let c0: u32 = peSrc[start+j].into();
                assert!( c0 < Q );
                let mut c1: u32 = peSrc[start+j+len].into();
                assert!( c1 < Q );

                let tmp = SymCryptMlKemModAdd( c0, c1 );
                c1 = SymCryptMlKemModSub( c1, c0 );
                c1 = SymCryptMlKemMontMul( c1, twiddleFactor, twiddleFactorMont );

                peSrc[start+j]      = tmp as u16;
                peSrc[start+j+len]  = c1 as u16;
            });
        }
    });
}

fn SymCryptMlKemPolyElementNTTLayer(peSrc: &mut POLYELEMENT, k: usize, len: usize) {
    SymCryptMlKemPolyElementNTTLayerC(peSrc, k, len);
}

fn SymCryptMlKemPolyElementINTTLayer(peSrc: &mut POLYELEMENT, k: usize, len: usize) {
    SymCryptMlKemPolyElementINTTLayerC(peSrc, k, len);
}

fn SymCryptMlKemPolyElementMulAndAccumulate(
    peSrc1: & POLYELEMENT,
    peSrc2: & POLYELEMENT,
    paDst: &mut POLYELEMENT_ACCUMULATOR )
{
    // FIXME
    c_for!(let mut i = 0; i < MLWE_POLYNOMIAL_COEFFICIENTS / 2; i += 1; {
        let a0: u32 = peSrc1[2*i].into();
        assert!( (a0 as u32) < Q );
        let a1: u32 = peSrc1[2*i+1].into();
        assert!( (a1 as u32) < Q );

        let b0: u32 = peSrc2[2*i  ].into();
        assert!( (b0 as u32) < Q );
        let b1: u32 = peSrc2[2*i+1].into();
        assert!( (b1 as u32) < Q );

        // SH: We are doing a matrix multiplication (and the matrix has a maximum
        // size of 4) which means we need to accumulate several products in the
        // target (at most 4 products).
        let mut c0: u32 = paDst[2*i].into();
        assert!( c0 <= 3*((3328*3328) + (3494*3312)) );
        let mut c1: u32 = paDst[(2*i)+1].into();
        assert!( c1 <= 3*((3328*3328) + (3494*3312)) );

        // multiplication results in range [0, 3328*3328]
        let mut a0b0: u32 = a0 * b0;
        let a1b1 = a1 * b1;
        let mut a0b1: u32 = a0 * b1;
        let a1b0 = a1 * b0;

        // we need a1*b1*zetaTwoTimesBitRevPlus1TimesR[i]
        // eagerly reduce a1*b1 with montgomery reduction
        // a1b1 = red(a1*b1) -> range [0,3494]
        //   (3494 is maximum result of first step of montgomery reduction of x*y for x,y in [0,3328])
        // we do not need to do final reduction yet
        // SH: how do we get the (very precise) bound 3494? Brute force.
        let inv : u32 = (a1b1 * NegQInvModR) & Rmask;
        // inv = (a1*b1 * (-Q^(-1) mod R)) % R
        let a1b1: u32 = (a1b1 + (inv * Q)) >> Rlog2; // in range [0, 3494]
        // a1b1 = (a1*b1 + a1*b1 * (-Q^(-1) mod R) * Q) / R
        //      = (a1*b1 * R^-1) mod Q
        assert!( a1b1 <= 3494 );

        // now multiply a1b1 by power of zeta
        let a1b1zetapow = a1b1 * (zetaTwoTimesBitRevPlus1TimesR[i] as u32);
        // a1b1zetapow = (a1*b1 * R^-1) * (Zeta^(2*BitRev(i) + 1) * R) mod Q
        //             = a1*b1 * Zeta^(2*BitRev(i) + 1) mod Q

        // sum pairs of products
        a0b0 += a1b1zetapow;    // a0*b0 + red(a1*b1)*zetapower in range [0, 3328*3328 + 3494*3312]
        assert!( a0b0 <= (3328*3328) + (3494*3312) );
        a0b1 += a1b0;           // a0*b1 + a1*b0                in range [0, 2*3328*3328]
        assert!( a0b1 <= 2*3328*3328 );

        // We sum at most 4 pairs of products into an accumulator in ML-KEM
        assert!( MATRIX_MAX_NROWS <= 4 );
        c0 += a0b0; // in range [0,4*3328*3328 + 4*3494*3312]
        assert!( c0 < (4*3328*3328) + (4*3494*3312) );
        c1 += a0b1; // in range [0,5*3328*3328 + 3*3494*3312]
        assert!( c1 < (5*3328*3328) + (3*3494*3312) );

        paDst[2*i  ] = c0;
        paDst[2*i+1] = c1;
    });
}

fn
SymCryptMlKemMontgomeryReduceAndAddPolyElementAccumulatorToPolyElement(
    paSrc: &mut POLYELEMENT_ACCUMULATOR,
    peDst: &mut POLYELEMENT)
{
    // FIXME
    c_for!(let mut i = 0; i < MLWE_POLYNOMIAL_COEFFICIENTS; i += 1; {
        let mut a = paSrc[i];
        assert!( a <= 4*((3328*3328) + (3494*3312)) );
        paSrc[i] = 0;

        let mut c: u32 = peDst[i].into();
        assert!( c < Q );

        // montgomery reduce sum of products
        let inv = (a * NegQInvModR) & Rmask;
        a = (a + (inv * Q)) >> Rlog2; // in range [0, 4711]
        assert!( a <= 4711 );

        // add destination
        c += a;
        assert!( c <= 8039 );

        // subtraction and conditional additions for constant time range reduction
        c -= 2*Q;           // in range [-2Q, 1381]
        assert!( (c >= ((-2*(Q as i32)) as u32)) || (c < 1381) );
        c += Q & (c >> 16); // in range [-Q, Q-1]
        assert!( (c >= ((-(Q as i32) as u32))) || (c < Q) );
        c += Q & (c >> 16); // in range [0, Q-1]
        assert!( c < Q );

        peDst[i] = c as u16;
    });
}

fn SymCryptMlKemPolyElementMulR(
    peSrc: & POLYELEMENT,
    peDst: &mut POLYELEMENT)
{
    // FIXME
    c_for!(let mut i = 0; i < MLWE_POLYNOMIAL_COEFFICIENTS; i += 1;
    {
        peDst[i] = SymCryptMlKemMontMul(
            peSrc[i].into(), Rsqr, RsqrTimesNegQInvModR ) as u16;
    });
}

fn SymCryptMlKemPolyElementAdd(
    peSrc1: & POLYELEMENT,
    peSrc2: & POLYELEMENT,
    peDst: & mut POLYELEMENT )
{
    // FIXME
    c_for!(let mut i = 0; i < MLWE_POLYNOMIAL_COEFFICIENTS; i += 1;
    {
        peDst[i] = SymCryptMlKemModAdd( peSrc1[i].into(), peSrc2[i].into() ) as u16;
    });
}

fn SymCryptMlKemPolyElementSub(
    peSrc1: & POLYELEMENT,
    peSrc2: & POLYELEMENT,
    peDst : & mut POLYELEMENT)
{
    c_for!(let mut i = 0; i < MLWE_POLYNOMIAL_COEFFICIENTS; i += 1;
    {
        peDst[i] = SymCryptMlKemModSub( peSrc1[i].into(), peSrc2[i].into() ) as u16;
    });
}

fn SymCryptMlKemPolyElementNTT(
    peSrc: &mut POLYELEMENT )
{
    SymCryptMlKemPolyElementNTTLayer( peSrc,  1, 128 );
    SymCryptMlKemPolyElementNTTLayer( peSrc,  2,  64 );
    SymCryptMlKemPolyElementNTTLayer( peSrc,  4,  32 );
    SymCryptMlKemPolyElementNTTLayer( peSrc,  8,  16 );
    SymCryptMlKemPolyElementNTTLayer( peSrc, 16,   8 );
    SymCryptMlKemPolyElementNTTLayer( peSrc, 32,   4 );
    SymCryptMlKemPolyElementNTTLayer( peSrc, 64,   2 );
}

// INTTFixupTimesRsqr = R^2 * 3303 = (3303<<32) mod Q
// 3303 constant is fixup from draft FIPS 203
// Multiplied by R^2 to additionally multiply coefficients by R after montgomery reduction
const INTTFixupTimesRsqr: u32 = 1441;
const INTTFixupTimesRsqrTimesNegQInvModR: u32 = 10079;

fn SymCryptMlKemPolyElementINTTAndMulR(
    peSrc: &mut POLYELEMENT )
{
    SymCryptMlKemPolyElementINTTLayer( peSrc, 127,   2 );
    SymCryptMlKemPolyElementINTTLayer( peSrc,  63,   4 );
    SymCryptMlKemPolyElementINTTLayer( peSrc,  31,   8 );
    SymCryptMlKemPolyElementINTTLayer( peSrc,  15,  16 );
    SymCryptMlKemPolyElementINTTLayer( peSrc,   7,  32 );
    SymCryptMlKemPolyElementINTTLayer( peSrc,   3,  64 );
    SymCryptMlKemPolyElementINTTLayer( peSrc,   1, 128 );

    c_for!(let mut i = 0; i < MLWE_POLYNOMIAL_COEFFICIENTS; i += 1;
    {
        peSrc[i] = SymCryptMlKemMontMul(
            peSrc[i].into(), INTTFixupTimesRsqr, INTTFixupTimesRsqrTimesNegQInvModR ) as u16;
    });
}

// ((1<<35) / Q)
//
// 1<<35 is the smallest power of 2 s.t. the constant has sufficient precision to round
// all inputs correctly in compression for all nBitsPerCoefficient < 12. A smaller
// constant could be used for smaller nBitsPerCoefficient for a small performance gain
//
const COMPRESS_MULCONSTANT: u32 = 0x9d7dbb;
const COMPRESS_SHIFTCONSTANT: u32 = 35;

// FIXME: can't use std::cmp::min due to required vs provided methods, tracked via https://github.com/AeneasVerif/charon/issues/180
// use std::cmp::min;
fn min(x: u32, y: u32) -> u32 { if x <= y { x } else { y } }

fn
SymCryptMlKemPolyElementCompressAndEncode(
    peSrc: & POLYELEMENT,
    nBitsPerCoefficient: u32,
    // _Out_writes_bytes_(nBitsPerCoefficient*(MLWE_POLYNOMIAL_COEFFICIENTS / 8))
    pbDst: &mut [u8] )
{
    let mut cbDstWritten: usize = 0;
    let mut accumulator: u32 = 0;
    let mut nBitsInAccumulator: u32 = 0;

    assert!( nBitsPerCoefficient >  0  );
    assert!( nBitsPerCoefficient <= 12 );

    c_for!(let mut i = 0; i < MLWE_POLYNOMIAL_COEFFICIENTS; i += 1;
    {
        let mut nBitsInCoefficient = nBitsPerCoefficient;
        let mut coefficient: u32 = peSrc[i].into(); // in range [0, Q-1]
        assert!( coefficient < Q );

        // first compress the coefficient
        // when nBitsPerCoefficient < 12 we compress per Compress_d in draft FIPS 203;
        if nBitsPerCoefficient < 12
        {
            // Multiply by 2^(nBitsPerCoefficient+1) / Q by multiplying by constant and shifting right
            let multiplication: u64 = (coefficient as u64) * (COMPRESS_MULCONSTANT as u64);
            coefficient = (multiplication >> (COMPRESS_SHIFTCONSTANT-(nBitsPerCoefficient+1))) as u32;

            // add "half" to round to nearest integer
            coefficient += 1;

            // final divide by two to get multiplication by 2^nBitsPerCoefficient / Q
            coefficient >>= 1;                              // in range [0, 2^nBitsPerCoefficient]
            assert!(coefficient <= (1<<nBitsPerCoefficient));

            // modular reduction by masking
            coefficient &= (1<<nBitsPerCoefficient)-1;    // in range [0, 2^nBitsPerCoefficient - 1]
            assert!(coefficient <  (1<<nBitsPerCoefficient));
        }

        // encode the coefficient
        // simple loop to add bits to accumulator and write accumulator to output
        #[inline]
        fn inner_loop(pbDst: &mut [u8], cbDstWritten: &mut usize, accumulator: &mut u32,
                      nBitsInAccumulator: &mut u32, nBitsInCoefficient: &mut u32, coefficient: &mut u32,
        ) {
            while {
                let nBitsToEncode = min(*nBitsInCoefficient, 32-*nBitsInAccumulator);

                let bitsToEncode = *coefficient & ((1<<nBitsToEncode)-1);
                *coefficient >>= nBitsToEncode;
                *nBitsInCoefficient -= nBitsToEncode;

                *accumulator |= bitsToEncode << *nBitsInAccumulator;
                *nBitsInAccumulator += nBitsToEncode;
                if *nBitsInAccumulator == 32
                {
                    pbDst[*cbDstWritten..*cbDstWritten+4].copy_from_slice(&u32::to_le_bytes(*accumulator));
                    *cbDstWritten += 4;
                    *accumulator = 0;
                    *nBitsInAccumulator = 0;
                };
                *nBitsInCoefficient > 0
            } {}
        }
        inner_loop(pbDst, &mut cbDstWritten, &mut accumulator, &mut nBitsInAccumulator, &mut nBitsInCoefficient, &mut coefficient);
    });

    assert!(nBitsInAccumulator == 0);
    assert!(cbDstWritten == (nBitsPerCoefficient*(MLWE_POLYNOMIAL_COEFFICIENTS as u32 / 8)) as usize);
}

enum MLKEM_ERROR { NO_ERROR, INVALID_BLOB }

// FIXME:
#[inline]
#[charon::opaque]
fn slice_to_sub_array<const N : usize>(s: &[u8], i: usize) -> [u8; N] {
    s[i..i+N].try_into().unwrap()
}


fn
SymCryptMlKemPolyElementDecodeAndDecompress(
    // _In_reads_bytes_(nBitsPerCoefficient*(MLWE_POLYNOMIAL_COEFFICIENTS / 8))
    pbSrc: &[u8],
    nBitsPerCoefficient: u32,
    peDst: &mut POLYELEMENT ) -> MLKEM_ERROR
{
    let mut cbSrcRead: usize = 0;
    let mut accumulator: u32 = 0;
    let mut nBitsInAccumulator: u32 = 0;

    assert!( nBitsPerCoefficient >  0  );
    assert!( nBitsPerCoefficient <= 12 );

    // FIXME
    c_for!(let mut i = 0; i < MLWE_POLYNOMIAL_COEFFICIENTS; i += 1;
    {
        let mut coefficient = 0;
        let mut nBitsInCoefficient = 0;

        // first gather and decode bits from pbSrc
        #[inline]
        fn inner_loop(pbSrc: &[u8], nBitsPerCoefficient: u32,
                      cbSrcRead: &mut usize, accumulator: &mut u32,
                      nBitsInAccumulator: &mut u32, coefficient: &mut u32,
                      nBitsInCoefficient: &mut u32) {
            while
            {
                if *nBitsInAccumulator == 0
                {
                    // FIXME
                    //*accumulator = u32::from_le_bytes(&pbSrc[*cbSrcRead..*cbSrcRead+4]).try_into().unwrap());
                    *accumulator = u32::from_le_bytes(slice_to_sub_array::<4>(pbSrc, *cbSrcRead));
                    *cbSrcRead += 4;
                    *nBitsInAccumulator = 32;
                }

                let nBitsToDecode = min(nBitsPerCoefficient-*nBitsInCoefficient, *nBitsInAccumulator);
                assert!(nBitsToDecode <= *nBitsInAccumulator);

                let bitsToDecode = *accumulator & ((1<<nBitsToDecode)-1);
                *accumulator >>= nBitsToDecode;
                *nBitsInAccumulator -= nBitsToDecode;

                *coefficient |= bitsToDecode << *nBitsInCoefficient;
                *nBitsInCoefficient += nBitsToDecode;
                nBitsPerCoefficient > *nBitsInCoefficient
            } {}
        }
        inner_loop(pbSrc, nBitsPerCoefficient, &mut cbSrcRead, &mut accumulator,
                   &mut nBitsInAccumulator, &mut coefficient, &mut nBitsInCoefficient);
        assert!(nBitsInCoefficient == nBitsPerCoefficient);

        // decompress the coefficient
        // when nBitsPerCoefficient < 12 we decompress per Decompress_d in draft FIPS 203
        // otherwise we perform input validation per 203 6.2 Input validation 2 (Modulus check)
        if nBitsPerCoefficient < 12
        {
            // Multiply by Q / 2^(nBitsPerCoefficient-1) by multiplying by constant and shifting right
            coefficient *= Q;
            coefficient >>= nBitsPerCoefficient-1;

            // add "half" to round to nearest integer
            coefficient += 1;

            // final divide by two to get multiplication by Q / 2^nBitsPerCoefficient
            coefficient >>= 1;  // in range [0, Q]

            // modular reduction by conditional subtraction
            coefficient = SymCryptMlKemModSub( coefficient, Q );
            assert!( coefficient < Q );
        }
        else if coefficient > Q
        {
            // input validation failure - this can happen with a malformed or corrupt encapsulation
            // or decapsulation key, but this validation failure only triggers on public data; we
            // do not need to be constant time
            return MLKEM_ERROR::INVALID_BLOB;
        }

        peDst[i] = coefficient as u16;
    });

    assert!(nBitsInAccumulator == 0);
    assert!(cbSrcRead == (nBitsPerCoefficient*(MLWE_POLYNOMIAL_COEFFICIENTS as u32 / 8)) as usize);

    MLKEM_ERROR::NO_ERROR
}

#[charon::opaque]
fn
SymCryptShake128Extract(
    _pState: &mut shake128State,
    _pbResult: &mut[u8],
    _bWipe: bool)
{
    panic!("TODO: stub");
}

fn SymCryptMlKemPolyElementSampleNTTFromShake128(
    pState: &mut shake128State,
    peDst: &mut POLYELEMENT )
{
    let mut i: usize = 0;
    let mut shakeOutputBuf = [0u8; 3*8]; // Keccak likes extracting multiples of 8-bytes
    let mut currBufIndex: usize = shakeOutputBuf.len();

    while i<MLWE_POLYNOMIAL_COEFFICIENTS
    {
        assert!(currBufIndex <= shakeOutputBuf.len());
        if currBufIndex == shakeOutputBuf.len()
        {
            // Note (Rust): shakeOutputBuf[..] seems unnecessary and trips Eurydice (FIXME, see #14)
            SymCryptShake128Extract(pState, &mut shakeOutputBuf, false);
            currBufIndex = 0;
        }

        let sample0 = u16::from_le_bytes(slice_to_sub_array::<2>(&shakeOutputBuf, currBufIndex)) & 0xfff;
        // TODO: Aeneas crashes if we comment the code below this line
        let sample1 = u16::from_le_bytes(slice_to_sub_array::<2>(&shakeOutputBuf, currBufIndex+1)) >> 4;
        currBufIndex += 3;

        peDst[i] = sample0;
        i += ((sample0 as u32) < Q) as usize;

        if i<MLWE_POLYNOMIAL_COEFFICIENTS
        {
            peDst[i] = sample1;
            i += ((sample1 as u32) < Q) as usize;
        }
    }
}

fn SymCryptMlKemPolyElementSampleCBDFromBytes(
    pbSrc: &[u8],
    eta: u32,
    peDst: &mut POLYELEMENT)
{
    // Note (Rust): using an index rather than incrementing pbSrc in place.
    let mut src_i = 0usize;
    assert!((eta == 2) || (eta == 3));
    if eta == 3
    {
        c_for!(let mut i = 0; i < MLWE_POLYNOMIAL_COEFFICIENTS; i += 1;
        {
            // unconditionally load 4 bytes into sampleBits, but only treat the load
            // as being 3 bytes (24-bits -> 4 coefficients) for eta==3 to align to
            // byte boundaries. Source buffer must be 1 byte larger than shake output
            let mut sampleBits = u32::from_le_bytes(slice_to_sub_array::<4>(pbSrc, src_i));
            src_i += 3;

            // sum bit samples - each consecutive slice of eta bits is summed together
            sampleBits = (sampleBits&0x249249) + ((sampleBits>>1)&0x249249) + ((sampleBits>>2)&0x249249);

            #[inline]
            fn then_inner_loop(peDst: &mut POLYELEMENT, i: usize, sampleBits: &mut u32) {
                c_for!(let mut j = 0; j < 4; j += 1;
                       {
                           // each coefficient is formed by taking the difference of two consecutive slices of eta bits
                           // the first eta bits are positive, the second eta bits are negative
                           let mut coefficient = *sampleBits & 0x3f;
                           *sampleBits >>= 6;
                           coefficient = (coefficient&3) - (coefficient>>3);
                           assert!((coefficient >= ((-3i32) as u32)) || (coefficient <= 3));

                           coefficient = coefficient + (Q & (coefficient >> 16));     // in range [0, Q-1]
                           assert!( coefficient < Q );

                           peDst[i+j] = coefficient as u16;
                       });
            }
            then_inner_loop(peDst, i, &mut sampleBits);
        });
    }
    else
    {
        c_for!(let mut i = 0; i < MLWE_POLYNOMIAL_COEFFICIENTS; i += 1;
        {
            // unconditionally load 4 bytes (32-bits -> 8 coefficients) into sampleBits
            let mut sampleBits = u32::from_le_bytes(slice_to_sub_array::<4>(pbSrc, src_i));
            src_i += 4;

            // sum bit samples - each consecutive slice of eta bits is summed together
            sampleBits = (sampleBits&0x55555555) + ((sampleBits>>1)&0x55555555);

            #[inline]
            fn else_inner_loop(peDst: &mut POLYELEMENT, i: usize, sampleBits: &mut u32) {
                c_for!(let mut j = 0; j < 8; j += 1;
                       {
                           // each coefficient is formed by taking the difference of two consecutive slices of eta bits
                           // the first eta bits are positive, the second eta bits are negative
                           let mut coefficient = *sampleBits & 0xf;
                           *sampleBits >>= 4;
                           coefficient = (coefficient&3) - (coefficient>>2);
                           assert!((coefficient >= (-2i32 as u32)) || (coefficient <= 2));

                           coefficient = coefficient + (Q & (coefficient >> 16));     // in range [0, Q-1]
                           assert!( coefficient < Q );

                           peDst[i+j] = coefficient as u16;
                       });
            }
            else_inner_loop(peDst, i, &mut sampleBits);
        });
    }
}

impl<'a> MATRIX<'a> {
    // Making this opaque because it uses nested borrows
    #[charon::opaque]
    fn
        swap(
            mut self,
            i:usize,
            j:usize) -> Self
    {
        self.apPolyElements.swap(i, j);
        self
    }
}

fn SymCryptMlKemMatrixTranspose(
    mut pmSrc: MATRIX )
    -> MATRIX
{
    let nRows = pmSrc.nRows;

    assert!( nRows >  0 );
    assert!( nRows <= MATRIX_MAX_NROWS );

    c_for!(let mut i = 0; i < nRows; i += 1;
    {
        #[inline]
        fn inner_loop(mut pmSrc: MATRIX, nRows: usize, i:usize) -> MATRIX {
            c_for!(let mut j = i+1; j < nRows; j += 1;
            {
                pmSrc = pmSrc.swap((i*nRows) + j, (j*nRows) + i);
            });
            pmSrc
        }
        pmSrc = inner_loop(pmSrc, nRows, i);
    });
    pmSrc
}

// FIXME: this requires nested borrows
#[charon::opaque]
#[inline]
fn SymCryptMlKemPolyElementMulAndAccumulate_aux<'a>(
    pmSrc1: MATRIX<'a>,
    nRows : usize,
    i: usize,
    j : usize,
    peSrc2: &POLYELEMENT,
    paTmp: &mut POLYELEMENT_ACCUMULATOR) -> MATRIX<'a> {
    let src1 : &POLYELEMENT = &pmSrc1.apPolyElements[(i*nRows) + j]; // FIXME: this requires nested borrows
    SymCryptMlKemPolyElementMulAndAccumulate(src1, peSrc2, paTmp );
    pmSrc1
}

// FIXME: we don't support nested borrows yet, meaning we
// have to move the matrix around
fn
SymCryptMlKemMatrixVectorMontMulAndAdd<'a, 'b, 'c>(
    mut pmSrc1: MATRIX<'a>, // TODO: &MATRIX
    pvSrc2: &VECTOR,
    pvDst: &mut VECTOR,
    paTmp: &mut POLYELEMENT_ACCUMULATOR
) -> MATRIX<'a>
{
    let nRows = pmSrc1.nRows;

    assert!( nRows >  0 );
    assert!( nRows <= MATRIX_MAX_NROWS );
    assert!( pvSrc2.len() == nRows );
    assert!( pvDst.len() == nRows );

    // Zero paTmp
    // FIXME
    // SymCryptWipeKnownSize( paTmp, INTERNAL_MLKEM_SIZEOF_POLYRINGELEMENT_ACCUMULATOR );

    c_for!(let mut i = 0; i < nRows; i += 1;
    {
        #[inline]
        fn inner_loop<'a>(mut pmSrc1: MATRIX<'a>, // TODO: &MATRIX
                      pvSrc2: &VECTOR,
                      paTmp: &mut POLYELEMENT_ACCUMULATOR,
                      nRows : usize,
                      i : usize,
        ) -> MATRIX<'a> {
            c_for!(let mut j = 0; j < nRows; j += 1;
            {
                pmSrc1 = SymCryptMlKemPolyElementMulAndAccumulate_aux(pmSrc1, nRows, i, j, &pvSrc2[i], paTmp );
            });
            pmSrc1
        }
        pmSrc1 = inner_loop(pmSrc1, pvSrc2, paTmp, nRows, i);

        // write accumulator to dest and zero accumulator
        SymCryptMlKemMontgomeryReduceAndAddPolyElementAccumulatorToPolyElement( paTmp, &mut pvDst[i] );
    });
    pmSrc1
}

// FIXME: moving values around because we don't support nested borrows
fn
SymCryptMlKemVectorMontDotProduct(
    pvSrc1: &mut VECTOR,
    pvSrc2: &mut VECTOR,
    peDst: &mut POLYELEMENT,
    paTmp: &mut POLYELEMENT_ACCUMULATOR )
{
    let nRows = pvSrc1.len();

    assert!( nRows >  0 );
    assert!( nRows <= MATRIX_MAX_NROWS );
    assert!( pvSrc2.len() == nRows );

    // Zero paTmp and peDst
    // FIXME
    // SymCryptWipeKnownSize( paTmp, INTERNAL_MLKEM_SIZEOF_POLYRINGELEMENT_ACCUMULATOR );
    // SymCryptWipeKnownSize( peDst, INTERNAL_MLKEM_SIZEOF_POLYRINGELEMENT );

    c_for!(let mut i = 0; i < nRows; i += 1;
    {
        SymCryptMlKemPolyElementMulAndAccumulate( &pvSrc1[i], &pvSrc2[i], paTmp );
    });

    // write accumulator to dest and zero accumulator
    SymCryptMlKemMontgomeryReduceAndAddPolyElementAccumulatorToPolyElement( paTmp, peDst );
}

fn
SymCryptMlKemVectorSetZero(
    pvSrc: &mut VECTOR
)
{
    let nRows = pvSrc.len();

    assert!( nRows >  0 );
    assert!( nRows <= MATRIX_MAX_NROWS );

    // FIXME
    // SymCryptWipe( (PBYTE) INTERNAL_MLKEM_VECTOR_ELEMENT( 0, pvSrc ), nRows*INTERNAL_MLKEM_SIZEOF_POLYRINGELEMENT );
}

fn
SymCryptMlKemVectorMulR(
    pvSrc: & VECTOR,
    pvDst: &mut VECTOR )
{
    let nRows = pvSrc.len();

    assert!( nRows >  0 );
    assert!( nRows <= MATRIX_MAX_NROWS );
    assert!( pvDst.len() == nRows );

    c_for!(let mut i = 0; i < nRows; i += 1;
    {
        SymCryptMlKemPolyElementMulR( & pvSrc[i], &mut pvDst[i] );
    });
}

fn
SymCryptMlKemVectorAdd(
    pvSrc1: &VECTOR,
    pvSrc2: &VECTOR,
    pvDst: &mut VECTOR )
{
    let nRows = pvSrc1.len();

    assert!( nRows >  0 );
    assert!( nRows <= MATRIX_MAX_NROWS );
    assert!( pvSrc2.len() == nRows );
    assert!( pvDst.len() == nRows );

    c_for!(let mut i = 0; i < nRows; i += 1;
    {
        SymCryptMlKemPolyElementAdd( &pvSrc1[i], &pvSrc2[i], &mut pvDst[i] );
    });
}

fn
SymCryptMlKemVectorSub(
    pvSrc1: &VECTOR,
    pvSrc2: &VECTOR,
    pvDst: &mut VECTOR )
{
    let nRows = pvSrc1.len();

    assert!( nRows >  0 );
    assert!( nRows <= MATRIX_MAX_NROWS );
    assert!( pvSrc2.len() == nRows );
    assert!( pvDst.len() == nRows );

    c_for!(let mut i = 0; i < nRows; i += 1;
    {
        SymCryptMlKemPolyElementSub( &pvSrc1[i], &pvSrc2[i], &mut pvDst[i] );
    });
}

fn
SymCryptMlKemVectorNTT(
    pvSrc: &mut VECTOR )
{
    let nRows = pvSrc.len();

    assert!( nRows >  0 );
    assert!( nRows <= MATRIX_MAX_NROWS );

    c_for!(let mut i = 0; i < nRows; i += 1;
    {
        SymCryptMlKemPolyElementNTT( & mut pvSrc[i] );
    });
}

fn
SymCryptMlKemVectorINTTAndMulR(
    pvSrc: &mut VECTOR )
{
    let nRows = pvSrc.len();

    assert!( nRows >  0 );
    assert!( nRows <= MATRIX_MAX_NROWS );

    c_for!(let mut i = 0; i < nRows; i += 1;
    {
        SymCryptMlKemPolyElementINTTAndMulR( &mut pvSrc[i] );
    });
}

fn
SymCryptMlKemVectorCompressAndEncode(
    pvSrc: &VECTOR,
    nBitsPerCoefficient: u32,
    pbDst: &mut[u8],
    cbDst: usize )
{
    let nRows = pvSrc.len();

    assert!( nRows >  0 );
    assert!( nRows <= MATRIX_MAX_NROWS );
    assert!( nBitsPerCoefficient >  0  );
    assert!( nBitsPerCoefficient <= 12 );
    assert!( cbDst == nRows*((nBitsPerCoefficient*(MLWE_POLYNOMIAL_COEFFICIENTS as u32 / 8)) as usize) );

    c_for!(let mut i = 0; i < nRows; i += 1;
    {
        // Note (Rust): had to change this to do range computation as opposed to in-place pointer
        // increment
        let pbDst_index = i * (nBitsPerCoefficient as usize)*(MLWE_POLYNOMIAL_COEFFICIENTS / 8);
        SymCryptMlKemPolyElementCompressAndEncode( & pvSrc[i], nBitsPerCoefficient, &mut pbDst[pbDst_index..]);
    });
}

fn
SymCryptMlKemVectorDecodeAndDecompress(
    pbSrc: &[u8],
    cbSrc: usize,
    nBitsPerCoefficient: u32,
    pvDst: &mut VECTOR ) -> MLKEM_ERROR
{
    let nRows = pvDst.len();

    assert!( nRows >  0 );
    assert!( nRows <= MATRIX_MAX_NROWS );
    assert!( nBitsPerCoefficient >  0  );
    assert!( nBitsPerCoefficient <= 12 );
    assert!( cbSrc == nRows*(nBitsPerCoefficient as usize)*(MLWE_POLYNOMIAL_COEFFICIENTS / 8) );

    c_for!(let mut i = 0; i < nRows; i += 1;
    {
        let pbSrc_index = i * (nBitsPerCoefficient as usize)*(MLWE_POLYNOMIAL_COEFFICIENTS / 8); 
        let scError = SymCryptMlKemPolyElementDecodeAndDecompress( &pbSrc[pbSrc_index..], nBitsPerCoefficient, &mut pvDst[i] );
        match scError { MLKEM_ERROR::NO_ERROR => return scError, _ => () };
    });
    MLKEM_ERROR::NO_ERROR
}
