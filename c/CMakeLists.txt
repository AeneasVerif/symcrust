project(test)

if(NOT MSVC)
    add_compile_options(
        -Wall
        -Wextra
        -Wno-unknown-pragmas
        $<$<CONFIG:DEBUG>:-g>
        $<$<CONFIG:DEBUG>:-Og>
        $<$<CONFIG:RELEASE>:-g>
        $<$<CONFIG:RELEASE>:-O3>
    )

    add_compile_options(-fsanitize=address)
    add_compile_options(-fsanitize=undefined)
    add_link_options(-fsanitize=address)
    add_link_options(-fsanitize=undefined)
endif(NOT MSVC)

if (NOT DEFINED ENV{KRML_HOME})
  message( FATAL_ERROR "Please define KRML_HOME" )
endif(NOT DEFINED ENV{KRML_HOME})

if (NOT DEFINED ENV{EURYDICE_HOME})
  message( FATAL_ERROR "Please define EURYDICE_HOME" )
endif(NOT DEFINED ENV{EURYDICE_HOME})

if (NOT DEFINED ENV{SYMCRYPT_LIB_PATH})
  message( FATAL_ERROR "Please define SYMCRYPT_LIB_PATH" )
endif(NOT DEFINED ENV{SYMCRYPT_LIB_PATH})

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_COLOR_DIAGNOSTICS "ON")

file(GLOB sources
  ${PROJECT_SOURCE_DIR}/common_shims.c
  ${PROJECT_SOURCE_DIR}/hash_shims.c
  ${PROJECT_SOURCE_DIR}/mlkem_shims.c
  ${PROJECT_SOURCE_DIR}/symcrust_common.c
  ${PROJECT_SOURCE_DIR}/symcrust_mlkem.c
  ${PROJECT_SOURCE_DIR}/test.c
)
# Add precompiler definitions like that:
# add_definitions(-DKRML_UNROLL_MAX=0)

add_executable(test ${sources})

target_link_directories(test PRIVATE $ENV{SYMCRYPT_LIB_PATH})
target_link_libraries(test PRIVATE symcrypt)

# Add more include directories if needed
target_include_directories(test PUBLIC "${CMAKE_SOURCE_DIR}/include" "${CMAKE_SOURCE_DIR}"
  "$ENV{KRML_HOME}/include" "$ENV{EURYDICE_HOME}/include" "$ENV{SYMCRYPT_LIB_PATH}/../../../inc")
