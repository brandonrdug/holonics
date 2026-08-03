cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)

project(holonics VERSION 0.0.0 LANGUAGES CXX CUDA)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_CUDA_STANDARD 20)
set(CMAKE_CUDA_STANDARD_REQUIRED ON)
set(CMAKE_CUDA_EXTENSIONS OFF)
set(CMAKE_CUDA_ARCHITECTURES 89)

if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release CACHE STRING "Pinned single-configuration profile" FORCE)
endif()
if(NOT CMAKE_BUILD_TYPE STREQUAL "Release")
  message(FATAL_ERROR "R0 production receipt requires CMAKE_BUILD_TYPE=Release")
endif()

include(cmake/VerifyToolchain.cmake)
holonics_verify_toolchain()

include(cmake/HolonicArchitecture.cmake)
holonics_define_owner_targets()

add_library(holonics_contract_options INTERFACE)
target_compile_options(
  holonics_contract_options
  INTERFACE
    $<$<COMPILE_LANGUAGE:CXX>:-O3;-Wall;-Wextra;-Wpedantic;-Werror;-Wconversion;-Wsign-conversion;-Wshadow;-fno-exceptions;-fno-rtti;-fno-fast-math;-ffp-contract=off;-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.;-ffile-prefix-map=${PROJECT_BINARY_DIR}=.>
    $<$<COMPILE_LANGUAGE:CUDA>:-O3;--fmad=false;--gpu-architecture=sm_89;--Werror=all-warnings;SHELL:-Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.>)

add_executable(r0_host_contract tests/compile_contracts/valid_host.cpp)
target_link_libraries(
  r0_host_contract
  PRIVATE
    holonics::event
    holonics::current
    holonics::receiver
    holonics::codec
    holonics::apparatus
    holonics_contract_options)

add_library(r0_device_contract OBJECT tests/compile_contracts/valid_device.cu)
target_link_libraries(
  r0_device_contract
  PRIVATE
    holonics::event
    holonics::current
    holonics::apparatus
    holonics_contract_options)

add_custom_target(
  r0_normalize_device_object
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_OBJECTS:r0_device_contract>
  DEPENDS r0_device_contract
  COMMAND_EXPAND_LISTS
  VERBATIM)

set(R0_GENERATED_DIRECTORY "${PROJECT_BINARY_DIR}/generated")
file(MAKE_DIRECTORY "${R0_GENERATED_DIRECTORY}")

set(R0_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/tests/compile_contracts/valid_device.cu")
file(
  GLOB_RECURSE R0_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.h"
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp"
  "${PROJECT_SOURCE_DIR}/include/holonics/*.cuh")
set(R0_DEVICE_COMMON_FLAGS
    --std=c++20
    -O3
    --gpu-architecture=sm_89
    --fmad=false
    --Werror=all-warnings
    -I${PROJECT_SOURCE_DIR}/include
    -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)

add_custom_command(
  OUTPUT "${R0_GENERATED_DIRECTORY}/r0_device_contract.ptx"
  COMMAND
    "${CMAKE_CUDA_COMPILER}" ${R0_DEVICE_COMMON_FLAGS} --ptx
    "${R0_DEVICE_SOURCE}" -o "${R0_GENERATED_DIRECTORY}/r0_device_contract.ptx"
  DEPENDS "${R0_DEVICE_SOURCE}" ${R0_DEVICE_HEADERS}
  VERBATIM)

add_custom_command(
  OUTPUT "${R0_GENERATED_DIRECTORY}/r0_device_contract.cubin"
  COMMAND
    "${CMAKE_CUDA_COMPILER}" ${R0_DEVICE_COMMON_FLAGS} --cubin
    "${R0_DEVICE_SOURCE}" -o "${R0_GENERATED_DIRECTORY}/r0_device_contract.cubin"
  DEPENDS "${R0_DEVICE_SOURCE}" ${R0_DEVICE_HEADERS}
  VERBATIM)

add_custom_target(
  r0_device_artifacts ALL
  DEPENDS
    "${R0_GENERATED_DIRECTORY}/r0_device_contract.ptx"
    "${R0_GENERATED_DIRECTORY}/r0_device_contract.cubin")

enable_testing()
include(cmake/R1Exact.cmake)

string(JOIN " " R0_DEVICE_FLAGS_RECEIPT ${R0_DEVICE_COMMON_FLAGS})
set(HOLONICS_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${R0_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/tests/compile_contracts/valid_device.cu -o <BUILD>/generated/r0_device_contract.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${R0_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/tests/compile_contracts/valid_device.cu -o <BUILD>/generated/r0_device_contract.cubin\n"
    ${R1_DECLARED_COMMANDS})
string(JOIN "" HOLONICS_DECLARED_COMMANDS_CONTENT ${HOLONICS_DECLARED_COMMANDS})
file(GENERATE
  OUTPUT "${R0_GENERATED_DIRECTORY}/declared_commands.txt"
  CONTENT "${HOLONICS_DECLARED_COMMANDS_CONTENT}")

set(HOLONICS_BUILD_MANIFEST "${PROJECT_BINARY_DIR}/receipts/BUILD_MANIFEST.txt")
add_custom_target(
  holonics_build_manifest ALL
  COMMAND
    "${CMAKE_COMMAND}"
    -DSOURCE_ROOT=${PROJECT_SOURCE_DIR}
    -DBUILD_ROOT=${PROJECT_BINARY_DIR}
    -DOUTPUT=${HOLONICS_BUILD_MANIFEST}
    -DCONSTRUCTION_PHASE=R1
    -DHOST_BINARY=$<TARGET_FILE:r0_host_contract>
    -DDEVICE_OBJECT=$<TARGET_OBJECTS:r0_device_contract>
    -DDEVICE_PTX=${R0_GENERATED_DIRECTORY}/r0_device_contract.ptx
    -DDEVICE_CUBIN=${R0_GENERATED_DIRECTORY}/r0_device_contract.cubin
    "-DEXTRA_ARTIFACTS=$<TARGET_FILE:r1_exact_device_deed>|${R1_DEVICE_PTX}|${R1_DEVICE_CUBIN}"
    -P "${PROJECT_SOURCE_DIR}/cmake/WriteBuildManifest.cmake"
  DEPENDS
    r0_host_contract
    r0_normalize_device_object
    r0_device_artifacts
    r1_normalize_executable
    r1_device_artifacts
    "${R0_GENERATED_DIRECTORY}/declared_commands.txt"
    "${PROJECT_SOURCE_DIR}/cmake/WriteBuildManifest.cmake"
  BYPRODUCTS "${HOLONICS_BUILD_MANIFEST}"
  COMMAND_EXPAND_LISTS
  VERBATIM)

add_custom_target(
  holonic-audit ALL
  COMMAND
    "${CMAKE_COMMAND}"
    -DSOURCE_ROOT=${PROJECT_SOURCE_DIR}
    -DBUILD_ROOT=${PROJECT_BINARY_DIR}
    -DMANIFEST=${HOLONICS_BUILD_MANIFEST}
    -DHOST_BINARY=$<TARGET_FILE:r0_host_contract>
    -DDEVICE_OBJECT=$<TARGET_OBJECTS:r0_device_contract>
    -DDEVICE_PTX=${R0_GENERATED_DIRECTORY}/r0_device_contract.ptx
    -DDEVICE_CUBIN=${R0_GENERATED_DIRECTORY}/r0_device_contract.cubin
    "-DEXTRA_ARTIFACTS=$<TARGET_FILE:r1_exact_device_deed>|${R1_DEVICE_PTX}|${R1_DEVICE_CUBIN}"
    -DEXTRA_DEVICE_PTX=${R1_DEVICE_PTX}
    -DEXTRA_DEVICE_CUBIN=${R1_DEVICE_CUBIN}
    -P "${PROJECT_SOURCE_DIR}/cmake/HolonicAudit.cmake"
  DEPENDS holonics_build_manifest
  VERBATIM)

include(cmake/HolonicContractTests.cmake)
