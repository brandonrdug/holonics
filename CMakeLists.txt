cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)

set(CMAKE_CUDA_FLAGS_INIT "--std=c++20")
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
include(cmake/R2Structure.cmake)
include(cmake/R3SourceTopology.cmake)
include(cmake/R4BodyLifecycle.cmake)
include(cmake/R5CausalCurrent.cmake)
include(cmake/R6ManyCurrentWeave.cmake)
include(cmake/R7CoreReceiverGeometry.cmake)
include(cmake/R8StatefulBoundaryCondensation.cmake)
include(cmake/R9AgnosticCodecsReflection.cmake)
include(cmake/R10ConditioningNativeMorphology.cmake)
include(cmake/R11MathematicalOccurrenceEcology.cmake)
include(cmake/R12GenerativeMathematicalCurrent.cmake)
include(cmake/R13LeanExteriorChecker.cmake)
include(cmake/R14FirstTheoremProduction.cmake)
include(cmake/R15ReturnConditionedMorphology.cmake)
include(cmake/R16TwoTheoremConversationalProduction.cmake)

string(JOIN " " R0_DEVICE_FLAGS_RECEIPT ${R0_DEVICE_COMMON_FLAGS})
set(HOLONICS_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${R0_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/tests/compile_contracts/valid_device.cu -o <BUILD>/generated/r0_device_contract.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${R0_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/tests/compile_contracts/valid_device.cu -o <BUILD>/generated/r0_device_contract.cubin\n"
    ${R1_DECLARED_COMMANDS}
    ${R2_DECLARED_COMMANDS}
    ${R3_DECLARED_COMMANDS}
    ${R4_DECLARED_COMMANDS}
    ${R5_DECLARED_COMMANDS}
    ${R6_DECLARED_COMMANDS}
    ${R7_DECLARED_COMMANDS}
    ${R8_DECLARED_COMMANDS}
    ${R9_DECLARED_COMMANDS}
    ${R10_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R11_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R12_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R13_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R14_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R15_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R16_DECLARED_COMMANDS})
string(JOIN "" HOLONICS_DECLARED_COMMANDS_CONTENT ${HOLONICS_DECLARED_COMMANDS})
file(GENERATE
  OUTPUT "${R0_GENERATED_DIRECTORY}/declared_commands.txt"
  CONTENT "${HOLONICS_DECLARED_COMMANDS_CONTENT}")

set(HOLONICS_BUILD_MANIFEST "${PROJECT_BINARY_DIR}/receipts/BUILD_MANIFEST.txt")
set(HOLONICS_EXTRA_ARTIFACTS
    "$<TARGET_FILE:r1_exact_device_deed>|${R1_DEVICE_PTX}|${R1_DEVICE_CUBIN}|$<TARGET_FILE:r2_structure_device_deed>|${R2_DEVICE_PTX}|${R2_DEVICE_CUBIN}|${R3_EXTRA_ARTIFACTS}|${R4_EXTRA_ARTIFACTS}|${R5_EXTRA_ARTIFACTS}|${R6_EXTRA_ARTIFACTS}|${R7_EXTRA_ARTIFACTS}|${R8_EXTRA_ARTIFACTS}|${R9_EXTRA_ARTIFACTS}|${R10_EXTRA_ARTIFACTS}|${R11_EXTRA_ARTIFACTS}|${R12_EXTRA_ARTIFACTS}|${R13_EXTRA_ARTIFACTS}|${R14_EXTRA_ARTIFACTS}|${R15_EXTRA_ARTIFACTS}|${R16_EXTRA_ARTIFACTS}")
set(HOLONICS_EXTRA_DEVICE_PTX "${R1_DEVICE_PTX}|${R2_DEVICE_PTX}|${R3_DEVICE_PTX}|${R4_DEVICE_PTX}|${R5_DEVICE_PTX}|${R6_DEVICE_PTX}|${R7_DEVICE_PTX}|${R8_DEVICE_PTX}|${R9_DEVICE_PTX}|${R10_DEVICE_PTX}|${R11_DEVICE_PTX}|${R12_DEVICE_PTX}|${R13_DEVICE_PTX_LIST}|${R14_DEVICE_PTX_LIST}|${R15_DEVICE_PTX_LIST}|${R16_DEVICE_PTX_LIST}")
set(HOLONICS_EXTRA_DEVICE_CUBIN "${R1_DEVICE_CUBIN}|${R2_DEVICE_CUBIN}|${R3_DEVICE_CUBIN}|${R4_DEVICE_CUBIN}|${R5_DEVICE_CUBIN}|${R6_DEVICE_CUBIN}|${R7_DEVICE_CUBIN}|${R8_DEVICE_CUBIN}|${R9_DEVICE_CUBIN}|${R10_DEVICE_CUBIN}|${R11_DEVICE_CUBIN}|${R12_DEVICE_CUBIN}|${R13_DEVICE_CUBIN_LIST}|${R14_DEVICE_CUBIN_LIST}|${R15_DEVICE_CUBIN_LIST}|${R16_DEVICE_CUBIN_LIST}")
add_custom_target(
  holonics_build_manifest ALL
  COMMAND
    "${CMAKE_COMMAND}"
    -DSOURCE_ROOT=${PROJECT_SOURCE_DIR}
    -DBUILD_ROOT=${PROJECT_BINARY_DIR}
    -DOUTPUT=${HOLONICS_BUILD_MANIFEST}
    -DCONSTRUCTION_PHASE=R16
    -DHOST_BINARY=$<TARGET_FILE:r0_host_contract>
    -DDEVICE_OBJECT=$<TARGET_OBJECTS:r0_device_contract>
    -DDEVICE_PTX=${R0_GENERATED_DIRECTORY}/r0_device_contract.ptx
    -DDEVICE_CUBIN=${R0_GENERATED_DIRECTORY}/r0_device_contract.cubin
    "-DEXTRA_ARTIFACTS=${HOLONICS_EXTRA_ARTIFACTS}"
    -P "${PROJECT_SOURCE_DIR}/cmake/WriteBuildManifest.cmake"
  DEPENDS
    r0_host_contract
    r0_normalize_device_object
    r0_device_artifacts
    r1_normalize_executable
    r1_device_artifacts
    r2_normalize_executable
    r2_device_artifacts
    r3_normalize_executable
    r3_device_artifacts
    r4_normalize_executable
    r4_device_artifacts
    r5_normalize_executable
    r5_device_artifacts
    r6_normalize_executable
    r6_device_artifacts
    r7_normalize_executable
    r7_device_artifacts
    r8_normalize_executable
    r8_device_artifacts
    r9_normalize_executable
    r9_device_artifacts
    r10_normalize_executable
    r10_device_artifacts
    r11_normalize_executable
    r11_device_artifacts
    r12_normalize_executable
    r12_device_artifacts
    r13_normalize_executable
    r13_device_artifacts
    r14_normalize_executable
    r14_device_artifacts
    r15_normalize_executable
    r15_device_artifacts
    r16_normalize_executable
    r16_device_artifacts
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
    "-DEXTRA_ARTIFACTS=${HOLONICS_EXTRA_ARTIFACTS}"
    "-DEXTRA_DEVICE_PTX=${HOLONICS_EXTRA_DEVICE_PTX}"
    "-DEXTRA_DEVICE_CUBIN=${HOLONICS_EXTRA_DEVICE_CUBIN}"
    -P "${PROJECT_SOURCE_DIR}/cmake/HolonicAudit.cmake"
  DEPENDS holonics_build_manifest
  VERBATIM)

include(cmake/HolonicContractTests.cmake)
