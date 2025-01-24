// We encapsulate the key in a separate module; this allows providing a modicum of abstraction, by
// only revealing the existence of certain fields and keeping others private.
//
// We offer several implementations, as this is the design phase; but we only pick one at
// compile-time so as to not generate polymorphic code.

use std::result::Result;

pub(crate)
enum MLKEM_ERROR { NO_ERROR, INVALID_BLOB, OUT_OF_MEMORY }

#[derive(PartialEq)]
pub(crate) enum PARAMS {
    // Rust: unclear if needed
    // PARAMS_NULL          = 0,
    MLKEM512      = 1,
    MLKEM768      = 2,
    MLKEM1024     = 3,
}

const SymCryptMlKemInternalParamsMlKem512: INTERNAL_PARAMS = INTERNAL_PARAMS
{
    params         : PARAMS::MLKEM512,
    nRows          : 2,
    nEta1          : 3,
    nEta2          : 2,
    nBitsOfU       : 10,
    nBitsOfV       : 4,
};

const SymCryptMlKemInternalParamsMlKem768: INTERNAL_PARAMS = INTERNAL_PARAMS
{
    params         : PARAMS::MLKEM768,
    nRows          : 3,
    nEta1          : 2,
    nEta2          : 2,
    nBitsOfU       : 10,
    nBitsOfV       : 4,
};

const SymCryptMlKemInternalParamsMlKem1024: INTERNAL_PARAMS = INTERNAL_PARAMS
{
    params         : PARAMS::MLKEM1024,
    nRows          : 4,
    nEta1          : 2,
    nEta2          : 2,
    nBitsOfU       : 11,
    nBitsOfV       : 5,
};

pub(crate)
const fn SymCryptMlKemkeyGetInternalParamsFromParams(
    params: PARAMS
) -> INTERNAL_PARAMS
{
    match params {
        | PARAMS::MLKEM512 =>
            SymCryptMlKemInternalParamsMlKem512,
        | PARAMS::MLKEM768 =>
            SymCryptMlKemInternalParamsMlKem768,
        | PARAMS::MLKEM1024 =>
            SymCryptMlKemInternalParamsMlKem1024
    }
}

pub(crate)
const MLWE_POLYNOMIAL_COEFFICIENTS: usize = 256;

const POLYELEMENT_ZERO: POLYELEMENT = [0; MLWE_POLYNOMIAL_COEFFICIENTS];

// PolyElements just store the coefficients without any header.
pub(crate)
type POLYELEMENT = [u16; MLWE_POLYNOMIAL_COEFFICIENTS ];

// The slice length is between 1 and MATRIX_MAX_NROWS.
// Note (Rust): unlike the original C code, we de-couple what we pass around (this type) vs. the
// underlying allocation (handled by the caller).
// Note (Rust): this already keeps the length -- no need for an additional field.
pub(crate)
type VECTOR = [POLYELEMENT];

pub(crate)
const KEY_MAX_SIZEOF_ENCODED_T: usize = 1536;

//
// MLKEMKEY type
//

pub(crate) struct INTERNAL_PARAMS {
    pub(crate) params: PARAMS,         // parameter set of ML-KEM being used, takes a value from PARAMS

    pub(crate) nRows: u8,           // corresponds to k from FIPS 203; the number of rows and columns in the matrix A,
                         // and the number of rows in column vectors s and t
    pub(crate) nEta1: u8,           // corresponds to eta_1 from FIPS 203; number of coinflips used in generating s and e
                                    // pub(crate)
                         // in keypair generation, and r in encapsulation
    pub(crate) nEta2: u8,           // corresponds to eta_2 from FIPS 203; number of coinflips used in generating e_1 and
                         // e_2 in encapsulation
    pub(crate) nBitsOfU: u8,        // corresponds to d_u from FIPS 203; number of bits that the coefficients of the polynomial
                         // ring elements of u are compressed to in encapsulation for encoding into ciphertext
    pub(crate) nBitsOfV: u8,        // corresponds to d_v from FIPS 203; number of bits that the coefficients of the polynomial
                         // ring element v is compressed to in encapsulation for encoding into ciphertext
}

/******************************************************************************
 * Option 1: using the Box type
 ******************************************************************************/

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
pub(crate) struct MATRIX {
    pub(crate) nRows: usize,
    pub(crate) apPolyElements: Box<[POLYELEMENT]>,
}

pub(crate)
struct KEY1 {
    pub(crate)
    fAlgorithmInfo: u32, // Tracks which algorithms the key can be used in
                         // Also tracks which per-key selftests have been performed on this key
                         // A bitwise OR of FLAG_KEY_*, FLAG_MLKEMKEY_*, and
                         // SELFTEST_KEY_* values

    pub(crate)
    params: INTERNAL_PARAMS,

    pub(crate)
    hasPrivateSeed: bool, // Set to true if key has the private seed (d)
    pub(crate)
    hasPrivateKey: bool,  // Set to true if key has the private key (s and z)

    // seeds
    pub(crate)
    privateSeed: [u8; 32],    // private seed (d) from which entire private PKE key can be derived
    pub(crate)
    privateRandom: [u8; 32],  // private random (z) used in implicit rejection

    pub(crate)
    publicSeed: [u8; 32],     // public seed (rho) from which A can be derived

    // misc fields
    pub(crate)
    encodedT: [u8; KEY_MAX_SIZEOF_ENCODED_T], // byte-encoding of public vector
                                                                              // may only use a prefix of this buffer
    pub(crate)
    encapsKeyHash: [u8; 32],  // Precomputed value of hash of ML-KEM's byte-encoding of encapsulation key

    // VARIABLE-LENGTH FIELDS, which we make private
    // 1. This forces clients to go through accessors, leaving us free to change the representation
    //    later on
    // 2. This prevents clients from directly building values of this type, or from mutating this
    //    fields, thus preserving our invariants.

    // A o s + e = t
    pmAtranspose: MATRIX,   // public matrix in NTT form (derived from publicSeed)
    pvt: Box<VECTOR>,        // public vector in NTT form
    pvs: Box<VECTOR>,        // private vector in NTT form

}

impl KEY1 {
    pub fn atranspose(&self) -> &[POLYELEMENT] {
        &self.pmAtranspose.apPolyElements
    }
    pub fn t(&self) -> &[POLYELEMENT] {
        &self.pvt
    }
    pub fn s(&self) -> &[POLYELEMENT] {
        &self.pvs
    }
    pub fn atranspose_mut(&mut self) -> &mut [POLYELEMENT] {
        &mut self.pmAtranspose.apPolyElements
    }
    pub fn t_mut(&mut self) -> &mut [POLYELEMENT] {
        &mut self.pvt
    }
    pub fn s_mut(&mut self) -> &mut [POLYELEMENT] {
        &mut self.pvs
    }
}

fn KeyAllocate1(params: PARAMS) -> Result<Box<KEY1>,MLKEM_ERROR>
{
    // Note (Rust): this function could previously fail. Now that we use an enum for the choice of
    // algorithm, match exhaustiveness checks obviate the need for an error code.
    let params = SymCryptMlKemkeyGetInternalParamsFromParams(params);
    let nRows = params.nRows;
    // Note (Rust): previously, returned a heap-allocated key. We create a Box here, but could also
    // return a value if we wanted, relying on LLVM to optimize out the copies of a large value.
    Result::Ok(Box::new(KEY1 {
        fAlgorithmInfo: 0u32,
        params,
        hasPrivateSeed: false,
        hasPrivateKey: false,
        privateSeed: [0; 32],
        privateRandom: [0; 32],
        publicSeed: [0; 32],
        // Note (Rust): this generates four boxes, see ALLOCATION.md for discussion
        // Note (Rust): the original C code performs null-checks to see if the allocations
        // succeeded. We could presumably use an error monad (the ? operator), Box::try_new, and
        // return a std::result::Result for this function (and others who need to perform
        // comparable checks).
        pmAtranspose: MATRIX {
            nRows: nRows as usize,
            apPolyElements: vec![POLYELEMENT_ZERO; (nRows * nRows) as usize].into()
        },
        pvt: vec![POLYELEMENT_ZERO; nRows as usize].into(),
        pvs: vec![POLYELEMENT_ZERO; nRows as usize].into(),
        encodedT: [0u8; KEY_MAX_SIZEOF_ENCODED_T],
        encapsKeyHash: [0u8; 32]
    }))
}


/******************************************************************************
 * Option 2: using a dynamically-sized type (DST), in safe Rust
 ******************************************************************************/

// This works only for ML-KEM because all of the variable-length types are arrays of POLYELEMENT.
// It also forces us to be a little more verbose because Rust does not allow allocating such a type
// when the length of the variable part is not a compile-time constant.

pub(crate)
struct PreKey2<U: ?Sized> {
    pub(crate) fAlgorithmInfo: u32,
    pub(crate) params: INTERNAL_PARAMS,
    pub(crate) hasPrivateSeed: bool,
    pub(crate) hasPrivateKey: bool,
    pub(crate) privateSeed: [u8; 32],
    pub(crate) privateRandom: [u8; 32],
    pub(crate) publicSeed: [u8; 32],
    pub(crate) encodedT: [u8; KEY_MAX_SIZEOF_ENCODED_T],
    pub(crate) encapsKeyHash: [u8; 32],

    // VARIABLE-LENGTH FIELDS
    nRows: usize, // note that this can be deduced from fAlgorithmInfo

    // Instantiated with U = [PolyElement], contains:
    // Atranspose, of length nRows * nRows 
    // t, of length nRows
    // s, of length nRows
    data: U,

}

pub(crate)
type KEY2 = PreKey2<[POLYELEMENT]>;

impl KEY2 {
    pub fn atranspose(&self) -> &[POLYELEMENT] {
        &self.data[0..2*self.nRows]
    }
    pub fn t(&self) -> &[POLYELEMENT] {
        &self.data[2*self.nRows..3*self.nRows]
    }
    pub fn s(&self) -> &[POLYELEMENT] {
        &self.data[3*self.nRows..4*self.nRows]
    }
    pub fn atranspose_mut(&mut self) -> &mut [POLYELEMENT] {
        &mut self.data[0..2*self.nRows]
    }
    pub fn t_mut(&mut self) -> &mut [POLYELEMENT] {
        &mut self.data[2*self.nRows..3*self.nRows]
    }
    pub fn s_mut(&mut self) -> &mut [POLYELEMENT] {
        &mut self.data[3*self.nRows..4*self.nRows]
    }
}

// This works, at the expense of a big copy-paste because Rust does not allow creating DSTs when
// the length of the data is not known at compile-time.
fn KeyAllocate2(params: PARAMS) -> Result<Box<KEY2>,MLKEM_ERROR> {
    match params {
        PARAMS::MLKEM512 => {
            const params: INTERNAL_PARAMS = SymCryptMlKemkeyGetInternalParamsFromParams(PARAMS::MLKEM512);
            const nRows: usize = params.nRows as usize;
            // !!! Make sure to build using &PreKey2, not &Key2, otherwise, the errors are really
            // hard to parse.
            Result::Ok(Box::new(PreKey2 {
                fAlgorithmInfo: 0u32,
                params,
                hasPrivateSeed: false,
                hasPrivateKey: false,
                privateSeed: [0; 32],
                privateRandom: [0; 32],
                publicSeed: [0; 32],
                encodedT: [0u8; KEY_MAX_SIZEOF_ENCODED_T],
                encapsKeyHash: [0u8; 32],
                nRows,
                data: [POLYELEMENT_ZERO; 4*nRows]
            }))
        },
        PARAMS::MLKEM768 => {
            const params: INTERNAL_PARAMS = SymCryptMlKemkeyGetInternalParamsFromParams(PARAMS::MLKEM768);
            const nRows: usize = params.nRows as usize;
            // !!! Make sure to build using &PreKey2, not &Key2, otherwise, the errors are really
            // hard to parse.
            Result::Ok(Box::new(PreKey2 {
                fAlgorithmInfo: 0u32,
                params,
                hasPrivateSeed: false,
                hasPrivateKey: false,
                privateSeed: [0; 32],
                privateRandom: [0; 32],
                publicSeed: [0; 32],
                encodedT: [0u8; KEY_MAX_SIZEOF_ENCODED_T],
                encapsKeyHash: [0u8; 32],
                nRows,
                data: [POLYELEMENT_ZERO; 4*nRows]
            }))
        },
        PARAMS::MLKEM1024 => {
            const params: INTERNAL_PARAMS = SymCryptMlKemkeyGetInternalParamsFromParams(PARAMS::MLKEM1024);
            const nRows: usize = params.nRows as usize;
            // !!! Make sure to build using &PreKey2, not &Key2, otherwise, the errors are really
            // hard to parse.
            Result::Ok(Box::new(PreKey2 {
                fAlgorithmInfo: 0u32,
                params,
                hasPrivateSeed: false,
                hasPrivateKey: false,
                privateSeed: [0; 32],
                privateRandom: [0; 32],
                publicSeed: [0; 32],
                encodedT: [0u8; KEY_MAX_SIZEOF_ENCODED_T],
                encapsKeyHash: [0u8; 32],
                nRows,
                data: [POLYELEMENT_ZERO; 4*nRows]
            }))
        },
        _ => panic!(""),
    }

}

/******************************************************************************
 * Option 3: relying on unsafe
 ******************************************************************************/

// TODO
//
// Design notes:
// - Rust cannot allocate DSTs when the size isn't known at compile-time, i.e. KeyAllocate2, above,
//   fails without the `const` on `nRows`
// - thus, we need to rely on unsafe to *even* create such an object;
//   https://docs.rs/slice-dst/latest/src/slice_dst/lib.rs.html#200-202 knows how to do that, we
//   should take inspiration from this code to correctly handle padding and alignment
// - speaking of which, we probably want to allocate a slice of u64s (rather than u8s) as the
//   variable-length slide at the end of the DST, so as to over-align and never worry about alignment
// - writing accessors requires the use of a cast

pub(crate)
type KEY3 = PreKey2<[u64]>;

impl KEY3 {
    pub fn atranspose(&self) -> &[POLYELEMENT] {
        unsafe {
            std::slice::from_raw_parts((&raw const self.data).cast::<POLYELEMENT>(), 2*self.nRows)
        }
    }
    pub fn t(&self) -> &[POLYELEMENT] {
        // Align on an 8-byte boundary, naturally.
        let t_start = (2*self.nRows + 7) / 8;
        unsafe {
            std::slice::from_raw_parts((&raw const self.data[t_start..]).cast::<POLYELEMENT>(), self.nRows)
        }
    }
    pub fn s(&self) -> &[POLYELEMENT] {
        // Align on an 8-byte boundary, naturally.
        let t_start = (2*self.nRows + 7) / 8;
        let s_start = t_start + (self.nRows + 7) / 8;
        unsafe {
            std::slice::from_raw_parts((&raw const self.data[s_start..]).cast::<POLYELEMENT>(), self.nRows)
        }
    }
    pub fn atranspose_mut(&mut self) -> &mut [POLYELEMENT] {
        unsafe {
            std::slice::from_raw_parts_mut((&raw mut self.data).cast::<POLYELEMENT>(), 2*self.nRows)
        }
    }
    pub fn t_mut(&mut self) -> &mut [POLYELEMENT] {
        // Align on an 8-byte boundary, naturally.
        let t_start = (2*self.nRows + 7) / 8;
        unsafe {
            std::slice::from_raw_parts_mut((&raw mut self.data[t_start..]).cast::<POLYELEMENT>(), self.nRows)
        }
    }
    pub fn s_mut(&mut self) -> &mut [POLYELEMENT] {
        // Align on an 8-byte boundary, naturally.
        let t_start = (2*self.nRows + 7) / 8;
        let s_start = t_start + (self.nRows + 7) / 8;
        unsafe {
            std::slice::from_raw_parts_mut((&raw mut self.data[s_start..]).cast::<POLYELEMENT>(), self.nRows)
        }
    }
}

// TODO: key allocation function that allocates raw memory

/******************************************************************************
 * API: static multiplexing
 ******************************************************************************/

// Pick your favorite option here for the sake of benchmarking.

pub(crate)
type KEY = KEY2; // EDIT HERE

pub(crate)
fn KeyAllocate(params: PARAMS) -> Result<Box<KEY>,MLKEM_ERROR> {
    KeyAllocate2(params) // EDIT HERE
}

// TODO: there is no free function, but it would presumably be needed by C callers -- can we figure
// something out, e.g. manually calling the drop trait for Box<KEY> with the understanding that Rust
// callers will not use this?
