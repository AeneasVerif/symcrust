# cmake -B build -G "Ninja Multi-Config"
# cmake --build build
# # For release (benchmarks)
# cmake --build build --config Release

cmake_minimum_required(VERSION 3.10)

project(test
    VERSION 0.1.0
    LANGUAGES C CXX
)

set(CMAKE_COLOR_DIAGNOSTICS "ON")

set(CMAKE_EXPORT_COMPILE_COMMANDS 1)

add_executable(test
    ${PROJECT_SOURCE_DIR}/test-symcrypt.c
)

if(DEFINED ENV{SYMCRYPT_LIB_PATH})
  message("Symcrypt path: $ENV{SYMCRYPT_LIB_PATH}")
  target_include_directories(test PRIVATE $ENV{SYMCRYPT_LIB_PATH}/../../../inc)
  target_link_directories(test PRIVATE $ENV{SYMCRYPT_LIB_PATH})
  target_link_libraries(test PRIVATE symcrypt)
else()
  error("Please define SYMCRYPT_LIB_PATH to path/to/SymCrypt/build/modules/generic")
endif(DEFINED ENV{SYMCRYPT_LIB_PATH})
