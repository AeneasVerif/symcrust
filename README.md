# Building SymCrypt (OSX)

Check out internal repository of SymCrypt, branch user/protz/osx_module (unmerged as of Feb 6th
2025). Run `scripts/build.py cmake --arch=arm64 --config=Release --no-fips --no-asm build`.

# Building this (OSX)

export SYMCRYPT_LIB_PATH=path/to/SymCrypt/build/module/generic
export DYLD_LIBRARY_PATH=path/to/SymCrypt/build/module/generic:$DYLD_LIBRARY_PATH
cargo build
cargo test
