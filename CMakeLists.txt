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

# This project has no C++20 modules. CMake nevertheless generated 132 dyndep
# scan files looking for them, and the graph that produced tripped a ninja
# assertion (Plan::RefreshDyndepDependents) on every build-graph change, which
# forced a full clean rebuild -- roughly eight minutes -- each time a header or
# target was added. Measured 2026-08-06: with scanning off there are zero dyndep
# files and a graph change rebuilds incrementally.
set(CMAKE_CXX_SCAN_FOR_MODULES OFF)

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
include(cmake/HolonicStanding.cmake)
include(cmake/R1Exact.cmake)
include(cmake/R2Structure.cmake)
include(cmake/R3SourceTopology.cmake)
include(cmake/R4BodyLifecycle.cmake)
include(cmake/R5CausalCurrent.cmake)
include(cmake/R6ManyCurrentWeave.cmake)
include(cmake/R7CoreReceiverGeometry.cmake)
include(cmake/R8StatefulBoundaryCondensation.cmake)
include(cmake/R9AgnosticCodecsReflection.cmake)
include(cmake/R11MathematicalOccurrenceEcology.cmake)
include(cmake/R18PhaseCrystalHypergeometry.cmake)
include(cmake/R19CharacteristicReturn.cmake)
include(cmake/R20RegularSingularContinuation.cmake)
include(cmake/R21BlindCharacteristicReconstruction.cmake)
include(cmake/R22CMNormOneIncidence.cmake)
include(cmake/R23ToricCycleClass.cmake)
include(cmake/R24AlgebraicVariation.cmake)
include(cmake/R25CausalLinearChain.cmake)
include(cmake/R26IntrinsicHypergeometry.cmake)
include(cmake/R27ExpressionGeometry.cmake)
include(cmake/R28HodgeRealization.cmake)
include(cmake/R29ArithmeticSpectral.cmake)
include(cmake/R30PluralRederivation.cmake)
include(cmake/R31CultivatedMathematicalOrgans.cmake)
include(cmake/R32ElementarySelfDerivation.cmake)
include(cmake/R33CharacteristicHypergeometry.cmake)
include(cmake/R34TraceFiber.cmake)
include(cmake/R35TraceRebase.cmake)
include(cmake/MovementAEnclosure.cmake)
include(cmake/PhaseSpine.cmake)
include(cmake/PhaseResidentMount.cmake)
include(cmake/PhaseTextMount.cmake)
include(cmake/ConditionedProduction.cmake)
include(cmake/ConstraintRebase.cmake)
include(cmake/OneStanding.cmake)
holonic_close_standing()

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
    ${R11_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R11_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS )
list(APPEND HOLONICS_DECLARED_COMMANDS )
list(APPEND HOLONICS_DECLARED_COMMANDS )
list(APPEND HOLONICS_DECLARED_COMMANDS )
list(APPEND HOLONICS_DECLARED_COMMANDS )
list(APPEND HOLONICS_DECLARED_COMMANDS )
list(APPEND HOLONICS_DECLARED_COMMANDS ${R18_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R19_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R20_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R21_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R22_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R23_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R24_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R25_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R26_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R27_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R28_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R29_DECLARED_COMMANDS})
list(APPEND HOLONICS_DECLARED_COMMANDS ${R30_DECLARED_COMMANDS} ${R31_DECLARED_COMMANDS}
  ${R32_DECLARED_COMMANDS} ${R33_DECLARED_COMMANDS} ${R34_DECLARED_COMMANDS}
  ${R35_DECLARED_COMMANDS} ${ENCLOSURE_DECLARED_COMMANDS} ${SPINE_DECLARED_COMMANDS} ${RESIDENT_DECLARED_COMMANDS} ${TEXT_DECLARED_COMMANDS})
string(JOIN "" HOLONICS_DECLARED_COMMANDS_CONTENT ${HOLONICS_DECLARED_COMMANDS})
file(GENERATE
  OUTPUT "${R0_GENERATED_DIRECTORY}/declared_commands.txt"
  CONTENT "${HOLONICS_DECLARED_COMMANDS_CONTENT}")

set(HOLONICS_BUILD_MANIFEST "${PROJECT_BINARY_DIR}/receipts/BUILD_MANIFEST.txt")
set(HOLONICS_EXTRA_ARTIFACTS
    "$<TARGET_FILE:r1_exact_device_deed>|${R1_DEVICE_PTX}|${R1_DEVICE_CUBIN}|$<TARGET_FILE:r2_structure_device_deed>|${R2_DEVICE_PTX}|${R2_DEVICE_CUBIN}|${R3_EXTRA_ARTIFACTS}|${R4_EXTRA_ARTIFACTS}|${R5_EXTRA_ARTIFACTS}|${R6_EXTRA_ARTIFACTS}|${R7_EXTRA_ARTIFACTS}|${R8_EXTRA_ARTIFACTS}|${R9_EXTRA_ARTIFACTS}|${R11_EXTRA_ARTIFACTS}|${R18_EXTRA_ARTIFACTS}|${R19_EXTRA_ARTIFACTS}|${R20_EXTRA_ARTIFACTS}|${R21_EXTRA_ARTIFACTS}|${R22_EXTRA_ARTIFACTS}|${R23_EXTRA_ARTIFACTS}|${R24_EXTRA_ARTIFACTS}|${R25_EXTRA_ARTIFACTS}|${R26_EXTRA_ARTIFACTS}|${R27_EXTRA_ARTIFACTS}|${R28_EXTRA_ARTIFACTS}|${R29_EXTRA_ARTIFACTS}|${R30_EXTRA_ARTIFACTS}|${R31_EXTRA_ARTIFACTS}|${R32_EXTRA_ARTIFACTS}|${R33_EXTRA_ARTIFACTS}|${R34_EXTRA_ARTIFACTS}|${R35_EXTRA_ARTIFACTS}|${ENCLOSURE_EXTRA_ARTIFACTS}|${SPINE_EXTRA_ARTIFACTS}|${RESIDENT_EXTRA_ARTIFACTS}|${TEXT_EXTRA_ARTIFACTS}")
set(HOLONICS_EXTRA_DEVICE_PTX "${R1_DEVICE_PTX}|${R2_DEVICE_PTX}|${R3_DEVICE_PTX}|${R4_DEVICE_PTX}|${R5_DEVICE_PTX}|${R6_DEVICE_PTX}|${R7_DEVICE_PTX}|${R8_DEVICE_PTX}|${R9_DEVICE_PTX}|${R11_DEVICE_PTX}|${R18_DEVICE_PTX_LIST}|${R19_DEVICE_PTX_LIST}|${R20_DEVICE_PTX_LIST}|${R21_DEVICE_PTX_LIST}|${R22_DEVICE_PTX_LIST}|${R23_DEVICE_PTX_LIST}|${R24_DEVICE_PTX_LIST}|${R25_DEVICE_PTX_LIST}|${R26_DEVICE_PTX_LIST}|${R27_DEVICE_PTX_LIST}|${R28_DEVICE_PTX_LIST}|${R29_DEVICE_PTX_LIST}|${R30_DEVICE_PTX_LIST}|${R31_DEVICE_PTX_LIST}|${R32_DEVICE_PTX_LIST}|${R33_DEVICE_PTX_LIST}|${R34_DEVICE_PTX_LIST}|${R35_DEVICE_PTX_LIST}|${ENCLOSURE_DEVICE_PTX_LIST}|${SPINE_DEVICE_PTX_LIST}|${RESIDENT_DEVICE_PTX_LIST}|${TEXT_DEVICE_PTX_LIST}")
set(HOLONICS_EXTRA_DEVICE_CUBIN "${R1_DEVICE_CUBIN}|${R2_DEVICE_CUBIN}|${R3_DEVICE_CUBIN}|${R4_DEVICE_CUBIN}|${R5_DEVICE_CUBIN}|${R6_DEVICE_CUBIN}|${R7_DEVICE_CUBIN}|${R8_DEVICE_CUBIN}|${R9_DEVICE_CUBIN}|${R11_DEVICE_CUBIN}|${R18_DEVICE_CUBIN_LIST}|${R19_DEVICE_CUBIN_LIST}|${R20_DEVICE_CUBIN_LIST}|${R21_DEVICE_CUBIN_LIST}|${R22_DEVICE_CUBIN_LIST}|${R23_DEVICE_CUBIN_LIST}|${R24_DEVICE_CUBIN_LIST}|${R25_DEVICE_CUBIN_LIST}|${R26_DEVICE_CUBIN_LIST}|${R27_DEVICE_CUBIN_LIST}|${R28_DEVICE_CUBIN_LIST}|${R29_DEVICE_CUBIN_LIST}|${R30_DEVICE_CUBIN_LIST}|${R31_DEVICE_CUBIN_LIST}|${R32_DEVICE_CUBIN_LIST}|${R33_DEVICE_CUBIN_LIST}|${R34_DEVICE_CUBIN_LIST}|${R35_DEVICE_CUBIN_LIST}|${ENCLOSURE_DEVICE_CUBIN_LIST}|${SPINE_DEVICE_CUBIN_LIST}|${RESIDENT_DEVICE_CUBIN_LIST}|${TEXT_DEVICE_CUBIN_LIST}")
add_custom_target(
  holonics_build_manifest ALL
  COMMAND
    "${CMAKE_COMMAND}"
    -DSOURCE_ROOT=${PROJECT_SOURCE_DIR}
    -DBUILD_ROOT=${PROJECT_BINARY_DIR}
    -DOUTPUT=${HOLONICS_BUILD_MANIFEST}
    -DCONSTRUCTION_PHASE=R35
    -DHOST_BINARY=$<TARGET_FILE:r0_host_contract>
    -DDEVICE_OBJECT=$<TARGET_OBJECTS:r0_device_contract>
    -DDEVICE_PTX=${R0_GENERATED_DIRECTORY}/r0_device_contract.ptx
    -DDEVICE_CUBIN=${R0_GENERATED_DIRECTORY}/r0_device_contract.cubin
    "-DEXTRA_ARTIFACTS=${HOLONICS_EXTRA_ARTIFACTS}"
    -P "${PROJECT_SOURCE_DIR}/cmake/WriteBuildManifest.cmake"
  DEPENDS
    enclosure_device_deed
    enclosure_device_artifacts
    spine_device_deed
    spine_device_artifacts
    resident_mount_deed
    resident_device_artifacts
    text_mount_deed
    text_device_artifacts
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
    r11_normalize_executable
    r11_device_artifacts
    r18_normalize_executable
    r18_device_artifacts
    r19_normalize_executable
    r19_device_artifacts
    r20_normalize_executable
    r20_device_artifacts
    r21_normalize_executable
    r21_device_artifacts
    r22_normalize_executable
    r22_device_artifacts
    r23_normalize_executable
    r23_device_artifacts
    r24_normalize_executable
    r24_device_artifacts
    r25_normalize_executable
    r25_device_artifacts
    r26_normalize_executable
    r26_device_artifacts
    r27_normalize_executable
    r27_device_artifacts
    r28_normalize_executable
    r28_device_artifacts
    r29_normalize_executable
    r29_device_artifacts
    r30_normalize_executable
    r30_device_artifacts
    r31_device_artifacts
    r32_device_artifacts
    r33_device_artifacts
    r34_device_artifacts
    r35_device_artifacts
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

set(HOLONICS_REACH_RECEIPT "${PROJECT_BINARY_DIR}/receipts/REACH_AUDIT.txt")
add_test(
  NAME r0.reach_audit
  COMMAND
    "${CMAKE_COMMAND}" -DSCAN_ROOT=${PROJECT_SOURCE_DIR}
    -DOUTPUT=${HOLONICS_REACH_RECEIPT}
    -P "${PROJECT_SOURCE_DIR}/cmake/HolonicReach.cmake")

# What is a test here, and what is not.
#
# ctest holds guards: source-tree audits, invariant falsifiers, compile
# contracts, host-contract checks. A guard asks a question of the tree that only
# running it can answer, and every one of them together is well under two
# minutes.
#
# ctest does NOT hold foundings. A deed, a replay, a seal, and a comparison all
# take files and found files; they belong to the build graph, where the closure
# decides whether they need to run. See cmake/HolonicStanding.cmake for the
# measurement that forced this and the certificate that licenses it.
#
#   ninja                      build code
#   ninja holonics_standing    bring the standing up to date; runs only what moved
#   ctest                      the guards
get_property(holonics_all_tests DIRECTORY PROPERTY TESTS)
foreach(holonics_test IN LISTS holonics_all_tests)
  string(REGEX REPLACE "\\..*$" "" holonics_group "${holonics_test}")
  set(holonics_label carrier)
  if(holonics_group STREQUAL "r0")
    set(holonics_label audit)
  elseif(holonics_group MATCHES
      "^(movement_a|phase_spine|phase_resident|phase_text|conditioned|constraint|standing)$")
    set(holonics_label spine)
  elseif(holonics_group MATCHES "^r([1-9][0-9])$")
    set(holonics_label frozen-math)
  endif()
  set_tests_properties("${holonics_test}" PROPERTIES LABELS "${holonics_label}")
endforeach()

# Test timeouts.
#
# Measured 2026-08-06: the heaviest deed runs 147 s standalone and carried
# TIMEOUT 300. Under -j 2 those deeds share one card, each stretches past 300,
# and ctest kills them -- producing failures that look like regressions and are
# contention. A 2x margin against a measured cost is a coin flip, not a limit.
#
# Timeouts exist to catch a hang, not to police a duration. They are now well
# clear of any measured cost; if a deed approaches one, that is a real hang.
