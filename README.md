# SymCrust (placeholder name)

A temporary repository to experiment with rewriting bits of SymCrypt in Rust, starting with ML-KEM.

# Build

You need SymCrypt: https://github.com/microsoft/SymCrypt.

- Windows, Linux: follow the SymCrypt build instructions
- OSX: check out the internal repository of SymCrypt, branch `user/protz/osx_module` (unmerged as of Feb 6th
  2025). Run `scripts/build.py cmake --arch=arm64 --config=Release --no-fips --no-asm build`.

Then, you need to set up a few environment variables.

```
export SYMCRYPT_INC_PATH=path/to/SymCrypt/inc
export SYMCRYPT_LIB_PATH=path/to/SymCrypt/dynamic/module
```

Then, you should be able to run:

```
cargo build
cargo test
```
