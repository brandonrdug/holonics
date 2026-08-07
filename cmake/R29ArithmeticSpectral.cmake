find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r29_arithmetic_store STATIC
  src/apparatus/host/arithmetic_spectral_card_adapter.cpp
  src/apparatus/host/arithmetic_spectral_store_adapter.cpp)
target_link_libraries(r29_arithmetic_store PRIVATE holonics::apparatus holonics_contract_options)

add_library(r29_arithmetic_executor STATIC
  src/apparatus/host/lean_checker_process.cpp
  src/cuda/executor/r29_arithmetic_spectral_executor.cu
  src/cuda/executor/r29_arithmetic_spectral_kernels.cu)
target_link_libraries(r29_arithmetic_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r29_arithmetic_spectral_device_deed
  src/apparatus/host/r29_arithmetic_spectral_deed.cpp
  tests/model/r29_artifact.cpp tests/model/r29_atlas.cpp tests/model/r29_cases.cpp
  tests/model/r29_reference.cpp tests/model/r29_reference_field.cpp tests/model/r29_verify.cpp)
target_include_directories(r29_arithmetic_spectral_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r29_arithmetic_spectral_device_deed PRIVATE holonics::apparatus
  holonics_contract_options r29_arithmetic_store r29_arithmetic_executor CUDA::cudart)

add_executable(r29_arithmetic_spectral_host_conformance
  tests/conformance/r29_arithmetic_spectral_host_conformance.cpp
  tests/model/r29_reference.cpp tests/model/r29_reference_field.cpp)
target_include_directories(r29_arithmetic_spectral_host_conformance PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r29_arithmetic_spectral_host_conformance
  PRIVATE holonics::event holonics_contract_options CUDA::cudart)

add_custom_target(r29_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r29_arithmetic_spectral_device_deed>
  DEPENDS r29_arithmetic_spectral_device_deed VERBATIM)

file(GLOB_RECURSE R29_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/*.hpp")
set(R29_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/r29_arithmetic_spectral_kernels.cu")
set(R29_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r29_arithmetic_spectral_kernels.ptx")
set(R29_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r29_arithmetic_spectral_kernels.cubin")
set(R29_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/src/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R29_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R29_DEVICE_COMMON_FLAGS} --ptx
    "${R29_DEVICE_SOURCE}" -o "${R29_DEVICE_PTX}"
  DEPENDS "${R29_DEVICE_SOURCE}" ${R29_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R29_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R29_DEVICE_COMMON_FLAGS} --cubin
    "${R29_DEVICE_SOURCE}" -o "${R29_DEVICE_CUBIN}"
  DEPENDS "${R29_DEVICE_SOURCE}" ${R29_DEVICE_HEADERS} VERBATIM)
add_custom_target(r29_device_artifacts ALL DEPENDS ${R29_DEVICE_PTX} ${R29_DEVICE_CUBIN})

string(JOIN " " R29_DEVICE_FLAGS_RECEIPT ${R29_DEVICE_COMMON_FLAGS})
set(R29_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R29_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r29_arithmetic_spectral_kernels.cu -o <BUILD>/generated/r29_arithmetic_spectral_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R29_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r29_arithmetic_spectral_kernels.cu -o <BUILD>/generated/r29_arithmetic_spectral_kernels.cubin\n"
  "checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R29_GENERATED_ARITHMETIC_SPECTRAL.olean <BUILD>/artifacts/R29_GENERATED_ARITHMETIC_SPECTRAL.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts" "${PROJECT_BINARY_DIR}/receipts")
set(R29_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R29_ARITHMETIC_SPECTRAL_DEED.txt")
set(R29_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R29_ARITHMETIC_SPECTRAL_HANDOFF.rest")
set(R29_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R29_GENERATED_ARITHMETIC_SPECTRAL.lean")
set(R29_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R29_GENERATED_ARITHMETIC_SPECTRAL.olean")
set(R29_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R29_LEAN_STDOUT.txt")
set(R29_STDERR "${PROJECT_BINARY_DIR}/artifacts/R29_LEAN_STDERR.txt")
set(R29_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R29_ARITHMETIC_SPECTRAL_ATLAS.tsv")
holonic_found(NAME r29.arithmetic_spectral_device_deed
  EXECUTABLE r29_arithmetic_spectral_device_deed
  COMMAND
    "${R29_DEED_ARTIFACT}" "${R28_FINAL_REST}" "${R29_FINAL_REST}"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R29_ARITHMETIC_SPECTRAL.card" "${R29_SOURCE}"
    "${R29_OLEAN}" "${R29_STDOUT}" "${R29_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R29_ATLAS}")
holonic_found(NAME r29.arithmetic_spectral_host_conformance
  EXECUTABLE r29_arithmetic_spectral_host_conformance
  COMMAND
   )
add_test(NAME r29.forbidden_arithmetic_spectral_copy COMMAND "${CMAKE_COMMAND}"
  -DCOMPILER=${CMAKE_CXX_COMPILER}
  -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_arithmetic_spectral_copy.cpp
  -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/src/include "-DEXPECTED_TEXT=use of deleted function"
  -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R29_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r29_arithmetic_spectral_device_deed>|${R29_DEVICE_PTX}|${R29_DEVICE_CUBIN}")
set(R29_DEVICE_PTX_LIST "${R29_DEVICE_PTX}")
set(R29_DEVICE_CUBIN_LIST "${R29_DEVICE_CUBIN}")
