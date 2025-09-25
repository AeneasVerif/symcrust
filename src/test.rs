// use std::io::Write;
use crate::common::Error;

#[allow(dead_code)]
#[test]
pub fn test_ffi() -> Result<(), Box<dyn std::error::Error>> {
    crate::common::init();

    let mut actual = [0u8; 64];
    let expected = [
        0xa6, 0x9f, 0x73, 0xcc, 0xa2, 0x3a, 0x9a, 0xc5, 0xc8, 0xb5, 0x67, 0xdc, 0x18, 0x5a, 0x75,
        0x6e, 0x97, 0xc9, 0x82, 0x16, 0x4f, 0xe2, 0x58, 0x59, 0xe0, 0xd1, 0xdc, 0xc1, 0x47, 0x5c,
        0x80, 0xa6, 0x15, 0xb2, 0x12, 0x3a, 0xf1, 0xf5, 0xf9, 0x4c, 0x11, 0xe3, 0xe9, 0x40, 0x2c,
        0x3a, 0xc5, 0x58, 0xf5, 0x00, 0x19, 0x9d, 0x95, 0xb6, 0xd3, 0xe3, 0x01, 0x75, 0x85, 0x86,
        0x28, 0x1d, 0xcd, 0x26, 
    ];
    crate::hash::sha3_512(&[0u8; 0], &mut actual);
    assert_eq!(actual, expected);

    let mut actual = [0u8; 64];
    let mut hs = crate::hash::UNINITIALIZED_HASH_STATE;
    // println!("hs addr: {:p}", &mut hs);
    // println!("internal hash state: {:?}", hs.ks.state);
    // std::io::stdout().flush();

    crate::hash::sha3_512_init(&mut hs);
    // println!("internal hash state: {:?}", hs.ks.state);
    crate::hash::sha3_512_result(&mut hs, &mut actual);
    // println!("internal hash state: {:?}", hs.ks.state);
    assert_eq!(actual, expected);

    let mut actual = [0u8; 128];
    let dst: &mut [u8; 64] = (&mut actual[0..64]).try_into().unwrap();
    crate::hash::sha3_512(&[0u8; 0], dst);
    assert_eq!(actual[0..64], expected);

    Ok(())
}

#[allow(dead_code)]
#[test]
pub fn test_api() -> Result<(), Box<dyn std::error::Error>> {
    crate::common::init();

    // KNOWN-ANSWER TEST
    let key_generation_seed = hex::decode("7c9935a0b07694aa0c6d10e4db6b1add2fd81a25ccb148032dcd739936737f2d8626ed79d451140800e03b59b956f8210e556067407d13dc90fa9e8b872bfb8f")?;
    assert_eq!(key_generation_seed.len(), 64);

    // Allocate + key-gen
    let mut k = crate::key::key_allocate(crate::key::Params::MlKem768)?;
    let r = crate::mlkem::key_set_value(&key_generation_seed, crate::key::Format::PrivateSeed, 0, &mut k);
    // TODO: ideally these would use std::result so that we can use the ? operator like we do for
    // hex::decode, below.
    if r != Error::NoError {
        return Err(Box::new(r))
    }

    // Read secret (a.k.a. decapsulation) key
    let mut secret_key = [0u8; crate::mlkem::sizeof_format_decapsulation_key(3)];
    
    let r = crate::mlkem::key_get_value(&k, &mut secret_key, crate::key::Format::DecapsulationKey, 0);
    if r != Error::NoError {
        return Err(Box::new(r))
    }
    let sha3_256_hash_of_secret_key = hex::decode("7deef44965b03d76de543ad6ef9e74a2772fa5a9fa0e761120dac767cf0152ef")?;
    let mut actual_sha3_256_hash_of_secret_key = [0u8; 32];
    crate::hash::sha3_256(&secret_key, &mut actual_sha3_256_hash_of_secret_key);
    assert_eq!(sha3_256_hash_of_secret_key, actual_sha3_256_hash_of_secret_key);

    println!("ek1 = {}", hex::encode_upper(secret_key));

    assert_eq!(0,1);
    // Read public (a.k.a. encapsulation) key
    let mut public_key = [0u8; crate::mlkem::sizeof_format_encapsulation_key(3)];
    let r = crate::mlkem::key_get_value(&k, &mut public_key, crate::key::Format::EncapsulationKey, 0);
    if r != Error::NoError {
        return Err(Box::new(r))
    }
    let sha3_256_hash_of_public_key = hex::decode("f57262661358cde8d3ebf990e5fd1d5b896c992ccfaadb5256b68bbf5943b132")?;
    let mut actual_sha3_256_hash_of_public_key = [0u8; 32];
    crate::hash::sha3_256(&public_key, &mut actual_sha3_256_hash_of_public_key);
    assert_eq!(sha3_256_hash_of_public_key, actual_sha3_256_hash_of_public_key);

    // Compute shared secret + ciphertext
    let encapsulation_seed = hex::decode("147c03f7a5bebba406c8fae1874d7f13c80efe79a3a9a874cc09fe76f6997615")?;
    let mut actual_shared_secret = [0u8; 32];
    let mut cipher_text = [0u8; 1088];
    let r = crate::mlkem::encapsulate_ex(&mut k, &encapsulation_seed, &mut actual_shared_secret, &mut cipher_text);
    if r != Error::NoError {
        return Err(Box::new(r))
    }
    let sha3_256_hash_of_ciphertext = hex::decode("6e777e2cf8054659136a971d9e70252f301226930c19c470ee0688163a63c15b")?;
    let mut actual_sha3_256_hash_of_ciphertext = [0u8; 32];
    crate::hash::sha3_256(&cipher_text, &mut actual_sha3_256_hash_of_ciphertext);
    assert_eq!(sha3_256_hash_of_ciphertext, actual_sha3_256_hash_of_ciphertext);
    let shared_secret = hex::decode("e7184a0975ee3470878d2d159ec83129c8aec253d4ee17b4810311d198cd0368")?;
    assert_eq!(shared_secret, actual_shared_secret);

    // Exercise decapsulation, and assert consistency
    let mut shared_secret2 = [0u8; 32];
    let r = crate::mlkem::decapsulate(&mut k, &cipher_text, &mut shared_secret2);
    if r != Error::NoError {
        return Err(Box::new(r))
    }
    assert_eq!(shared_secret2, actual_shared_secret);

    // Functional test -- should roundtrip!
    let mut k = crate::key::key_allocate(crate::key::Params::MlKem768)?;
    crate::mlkem::key_generate(&mut k, 0);
    let mut secret = [0u8; 32];
    let mut cipher = [0u8; 1088];
    crate::mlkem::encapsulate(&mut k, &mut secret, &mut cipher);

    let mut secret2 = [0u8; 32];
    crate::mlkem::decapsulate(&mut k, &cipher, &mut secret2);
    assert_eq!(secret, secret2);

    // Perf test -- simplistic
    let mut k = crate::key::key_allocate(crate::key::Params::MlKem768)?;
    for i in 0..1000u32 {
        crate::mlkem::key_generate(&mut k, 0);
        let mut secret = [(i % 256) as u8; 32];
        let mut cipher = [0u8; 1088];
        crate::mlkem::encapsulate(&mut k, &mut secret, &mut cipher);

        let mut secret2 = [(i % 256) as u8; 32];
        crate::mlkem::decapsulate(&mut k, &cipher, &mut secret2);
        assert_eq!(secret, secret2);
    }


    Ok(())
}

#[allow(dead_code)]
#[test]
pub fn test_acvp() -> Result<(), Box<dyn std::error::Error>> {
    crate::common::init();

    println!("test vector 1.1 for keygen");

    let zd_seed = hex::decode(concat!(
        "BBA3C0F5DF044CDF4D9CAA53CA15FDE26F34EB3541555CFC54CA9C31B964D0C8",
        "0A64FDD51A8D91B3166C4958A94EFC3166A4F5DF680980B878DB8371B7624C96"
    ))?;
    assert_eq!(zd_seed.len(), 64);
    
    let ek0 = hex::decode("1CAB32BE749CA76124EE19907B9CCB7FD30F8B2C38DC970E81F9956C97A8BD3C6E37B07C29E60BB2B75C5258B572626A859ABA89DB3AABC571424618B26310278B8EC4E76ED07A10B864AABF37BFC9F364731050631421BFCB1C3B9153D4316A95089197A027AB80B39C362CE6D97EFF422244FB81AAF67354F03894CC25B2707939A4A06D302C59D106EB743678DAA3F1D1C3F46B03F0DAA0641835A548363180744E6B6235B84DB9A4628279A6EF7231499208E657A3F9BB6E3F782606B79FC9A38723576FA80898E8A6887D94C3ED774E46A86CFE705B34C6B5535865329C5A4A820F9114CE9A9C68495C726368B9E073CBBE627A7DE419F7F7B4AD221576F91FB1E66CFF9651BD6C25E3CC9CA49A570CF041E457658072B684E714BD6A86B3D05C7597A729E12E512C8D7E5B5C27049EFB0AC0E085B1B88347BFD314B4E4AB4B8875A489ADB8C9AE28008BAD36AAAD24683563BFAF19BDA8677AB7BAC7E33C3087B84A45246A2AB1AEF397750D386ACDAC63C87506166A0FAE18773F530E74545D54BC670DD7353B75B16373CB8A6269AF37097EE1B1640458153132AD80AB64F7A599B8670E301205043C136C56CA5A06DBFABA3204671C1B237B18824555B5DDB206A74ACE637005B363238378BDA5E198AD69B85CBB399E8B07CB899F9E93CF6CF62FCAFC9E4D77363CA2149E92197F2133223799C182CF5F182ECD35B5FDFCBF0A93A1350198F2F244F3216B442A22FDDB2F4F3BB8CBF0168D0220AA725A0E287DF08079A1DBB8747C02F0C2C829759A5D95B6237522E7F71AB5669390377E03A93AB7FC7E9FD6BB59C1B9B8CC966141B0BA6796E66829D6A403B1F5816C8557EE8841031B2ED6C6CCFE8A55B39B9273F8BA050B1B328C7B9A238A7B8324F16A7A474C0B5721B9C8246531E19208838356F3337768BCB3397B4E01CC26175B67A66DFCD11F07B295C20AB484A60E7D086DB39B8301845B654A484462508FA78506357BBBF42DBAC157BCA7769C099A0B1894D4A17256F504EBE50BE284656F653845A26B00856D76A8A5A166CD09D04705261EBAFA20687A1068D9B9E28326848B67A0A3994D2DBA4B7A8F623B901E17CBEE610847A2903301C58287")?;
    assert_eq!(ek0.len(), crate::mlkem::sizeof_format_decapsulation_key(3));

    // Allocate + key-gen
    let mut k = crate::key::key_allocate(crate::key::Params::MlKem512)?;
    let r = crate::mlkem::key_set_value(&zd_seed, crate::key::Format::PrivateSeed, 0, &mut k);
    // TODO: ideally these would use std::result so that we can use the ? operator like we do for
    // hex::decode, below.
    if r != Error::NoError {
        return Err(Box::new(r))
    }

    // Read secret (a.k.a. decapsulation) key
    let mut secret_key = [0u8; crate::mlkem::sizeof_format_decapsulation_key(3)];
    let r = crate::mlkem::key_get_value(&k, &mut secret_key, crate::key::Format::DecapsulationKey, 0);
    if r != Error::NoError {
        return Err(Box::new(r))
    }
    
    println!("ek0 = {}", hex::encode_upper(ek0));
    println!("ek1 = {}", hex::encode_upper(secret_key));
    // assert_eq!(sha3_256_hash_of_secret_key, actual_sha3_256_hash_of_secret_key);

    /* 
    // Read public (a.k.a. encapsulation) key
    let mut public_key = [0u8; crate::mlkem::sizeof_format_encapsulation_key(3)];
    let r = crate::mlkem::key_get_value(&k, &mut public_key, crate::key::Format::EncapsulationKey, 0);
    if r != Error::NoError {
        return Err(Box::new(r))
    }
    let sha3_256_hash_of_public_key = hex::decode("f57262661358cde8d3ebf990e5fd1d5b896c992ccfaadb5256b68bbf5943b132")?;
    let mut actual_sha3_256_hash_of_public_key = [0u8; 32];
    crate::hash::sha3_256(&public_key, &mut actual_sha3_256_hash_of_public_key);
    assert_eq!(sha3_256_hash_of_public_key, actual_sha3_256_hash_of_public_key);

    // Compute shared secret + ciphertext
    let encapsulation_seed = hex::decode("147c03f7a5bebba406c8fae1874d7f13c80efe79a3a9a874cc09fe76f6997615")?;
    let mut actual_shared_secret = [0u8; 32];
    let mut cipher_text = [0u8; 1088];
    let r = crate::mlkem::encapsulate_ex(&mut k, &encapsulation_seed, &mut actual_shared_secret, &mut cipher_text);
    if r != Error::NoError {
        return Err(Box::new(r))
    }
    let sha3_256_hash_of_ciphertext = hex::decode("6e777e2cf8054659136a971d9e70252f301226930c19c470ee0688163a63c15b")?;
    let mut actual_sha3_256_hash_of_ciphertext = [0u8; 32];
    crate::hash::sha3_256(&cipher_text, &mut actual_sha3_256_hash_of_ciphertext);
    assert_eq!(sha3_256_hash_of_ciphertext, actual_sha3_256_hash_of_ciphertext);
    let shared_secret = hex::decode("e7184a0975ee3470878d2d159ec83129c8aec253d4ee17b4810311d198cd0368")?;
    assert_eq!(shared_secret, actual_shared_secret);

    // Exercise decapsulation, and assert consistency
    let mut shared_secret2 = [0u8; 32];
    let r = crate::mlkem::decapsulate(&mut k, &cipher_text, &mut shared_secret2);
    if r != Error::NoError {
        return Err(Box::new(r))
    }
    assert_eq!(shared_secret2, actual_shared_secret);

    // Functional test -- should roundtrip!
    let mut k = crate::key::key_allocate(crate::key::Params::MlKem768)?;
    crate::mlkem::key_generate(&mut k, 0);
    let mut secret = [0u8; 32];
    let mut cipher = [0u8; 1088];
    crate::mlkem::encapsulate(&mut k, &mut secret, &mut cipher);

    let mut secret2 = [0u8; 32];
    crate::mlkem::decapsulate(&mut k, &cipher, &mut secret2);
    assert_eq!(secret, secret2);

    // Perf test -- simplistic
    let mut k = crate::key::key_allocate(crate::key::Params::MlKem768)?;
    for i in 0..1000u32 {
        crate::mlkem::key_generate(&mut k, 0);
        let mut secret = [(i % 256) as u8; 32];
        let mut cipher = [0u8; 1088];
        crate::mlkem::encapsulate(&mut k, &mut secret, &mut cipher);

        let mut secret2 = [(i % 256) as u8; 32];
        crate::mlkem::decapsulate(&mut k, &cipher, &mut secret2);
        assert_eq!(secret, secret2);
    }
    */

    Ok(())
}