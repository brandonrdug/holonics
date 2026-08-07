find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r18_phase_crystal_store STATIC
  src/apparatus/host/phase_crystal_store_adapter.cpp)
target_link_libraries(r18_phase_crystal_store
  PRIVATE holonics::apparatus holonics_contract_options)

add_library(r18_phase_crystal_executor STATIC
  src/apparatus/host/lean_checker_process.cpp
  src/cuda/executor/r18_phase_crystal_executor.cu
  src/cuda/executor/r18_phase_crystal_kernels.cu)
target_link_libraries(r18_phase_crystal_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r18_phase_crystal_device_deed
  src/apparatus/host/r18_phase_crystal_deed.cpp
  tests/model/r18_artifact.cpp
  tests/model/r18_cases.cpp
  tests/model/r18_verify.cpp)
target_include_directories(r18_phase_crystal_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r18_phase_crystal_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r18_phase_crystal_store
    r18_phase_crystal_executor CUDA::cudart)

add_executable(r18_phase_crystal_host_conformance
  tests/conformance/r18_phase_crystal_host_conformance.cpp
  tests/model/r18_cases.cpp)
target_include_directories(r18_phase_crystal_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r18_phase_crystal_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r18_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r18_phase_crystal_device_deed>
  DEPENDS r18_phase_crystal_device_deed VERBATIM)

file(GLOB_RECURSE R18_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/*.hpp")
set(R18_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/r18_phase_crystal_kernels.cu")
set(R18_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r18_phase_crystal_kernels.ptx")
set(R18_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r18_phase_crystal_kernels.cubin")
set(R18_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/src/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R18_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R18_DEVICE_COMMON_FLAGS} --ptx
    "${R18_DEVICE_SOURCE}" -o "${R18_DEVICE_PTX}"
  DEPENDS "${R18_DEVICE_SOURCE}" ${R18_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R18_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R18_DEVICE_COMMON_FLAGS} --cubin
    "${R18_DEVICE_SOURCE}" -o "${R18_DEVICE_CUBIN}"
  DEPENDS "${R18_DEVICE_SOURCE}" ${R18_DEVICE_HEADERS} VERBATIM)
add_custom_target(r18_device_artifacts ALL DEPENDS ${R18_DEVICE_PTX} ${R18_DEVICE_CUBIN})

string(JOIN " " R18_DEVICE_FLAGS_RECEIPT ${R18_DEVICE_COMMON_FLAGS})
set(R18_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R18_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r18_phase_crystal_kernels.cu -o <BUILD>/generated/r18_phase_crystal_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R18_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r18_phase_crystal_kernels.cu -o <BUILD>/generated/r18_phase_crystal_kernels.cubin\n"
  "exterior_checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R18_GENERATED_PHASE_CRYSTAL.olean <BUILD>/artifacts/R18_GENERATED_PHASE_CRYSTAL.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts")

# The inherited predecessor is founded, not committed. See
# src/apparatus/host/inherited_predecessor_deed.cpp for why the 320-octet blob it
# replaces could not survive a layout change.
add_executable(inherited_predecessor_deed
  src/apparatus/host/inherited_predecessor_deed.cpp tests/model/r18_cases.cpp)
target_include_directories(inherited_predecessor_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(inherited_predecessor_deed
  PRIVATE holonics::apparatus holonics_contract_options)
set(INHERITED_PREDECESSOR "${PROJECT_BINARY_DIR}/artifacts/INHERITED_PREDECESSOR.rest")
holonic_found(NAME inherited.predecessor
  EXECUTABLE inherited_predecessor_deed
  COMMAND "${INHERITED_PREDECESSOR}")

set(R18_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R18_PHASE_CRYSTAL_DEED.txt")
set(R18_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R18_PHASE_CRYSTAL_HANDOFF.rest")
set(R18_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R18_GENERATED_PHASE_CRYSTAL.lean")
set(R18_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R18_GENERATED_PHASE_CRYSTAL.olean")
set(R18_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R18_LEAN_STDOUT.txt")
set(R18_STDERR "${PROJECT_BINARY_DIR}/artifacts/R18_LEAN_STDERR.txt")
set(R18_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R18_PHASE_CRYSTAL_ATLAS.tsv")
holonic_found(NAME r18.phase_crystal_device_deed
  EXECUTABLE r18_phase_crystal_device_deed
  COMMAND
    "${R18_DEED_ARTIFACT}"
    "${INHERITED_PREDECESSOR}" "${R18_FINAL_REST}"
    "${R18_SOURCE}" "${R18_OLEAN}" "${R18_STDOUT}" "${R18_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R18_ATLAS}")
holonic_found(NAME r18.phase_crystal_host_conformance
  EXECUTABLE r18_phase_crystal_host_conformance
  COMMAND
   )
add_test(NAME r18.forbidden_phase_crystal_copy
  COMMAND "${CMAKE_COMMAND}" -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_phase_crystal_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/src/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R18_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r18_phase_crystal_device_deed>|${R18_DEVICE_PTX}|${R18_DEVICE_CUBIN}")
set(R18_DEVICE_PTX_LIST "${R18_DEVICE_PTX}")
set(R18_DEVICE_CUBIN_LIST "${R18_DEVICE_CUBIN}")
