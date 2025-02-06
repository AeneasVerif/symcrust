// use hex;
use crate::common::*;
use std::result::*;

#[test]
pub fn test() -> Result<(), MLKEM_ERROR> {

    // Functional test
    let mut k = crate::key::KeyAllocate(crate::key::PARAMS::MLKEM768)?;
    let mut secret = [0u8; 32];
    let mut cipher = [0u8; 1088];
    crate::mlkem::SymCryptMlKemEncapsulate(&mut k, &mut secret, &mut cipher);

    let mut secret2 = [0u8; 32];
    crate::mlkem::SymCryptMlKemDecapsulate(&mut k, &cipher, &mut secret2);
    assert_eq!(secret, secret2);

    // Known-answer test
    // let key_generation_seed = hex::decode("7c9935a0b07694aa0c6d10e4db6b1add2fd81a25ccb148032dcd739936737f2d8626ed79d451140800e03b59b956f8210e556067407d13dc90fa9e8b872bfb8f")?;
    // let sha3_256_hash_of_public_key = hex::decode("f57262661358cde8d3ebf990e5fd1d5b896c992ccfaadb5256b68bbf5943b132")?;
    // let sha3_256_hash_of_secret_key = hex::decode("7deef44965b03d76de543ad6ef9e74a2772fa5a9fa0e761120dac767cf0152ef")?;
    // let encapsulation_seed = hex::decode("147c03f7a5bebba406c8fae1874d7f13c80efe79a3a9a874cc09fe76f6997615")?;
    // let sha3_256_hash_of_ciphertext = hex::decode("6e777e2cf8054659136a971d9e70252f301226930c19c470ee0688163a63c15b")?;
    // let shared_secret = hex::decode("e7184a0975ee3470878d2d159ec83129c8aec253d4ee17b4810311d198cd0368")?;
    Ok(())
}
