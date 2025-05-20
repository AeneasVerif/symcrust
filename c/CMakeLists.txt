project(test)

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

# Change path from /src if needed, or add more directories
file(GLOB_RECURSE sources
        "${CMAKE_SOURCE_DIR}/*.c"
        )
# Add precompiler definitions like that:
# add_definitions(-DKRML_UNROLL_MAX=0)

add_executable(test ${sources})

target_link_directories(test PRIVATE $ENV{SYMCRYPT_LIB_PATH})
target_link_libraries(test PRIVATE symcrypt)

# Add more include directories if needed
target_include_directories(test PUBLIC "${CMAKE_SOURCE_DIR}/include" "${CMAKE_SOURCE_DIR}"
  "$ENV{KRML_HOME}/include" "$ENV{EURYDICE_HOME}/include" "$ENV{SYMCRYPT_LIB_PATH}/../../../include")
