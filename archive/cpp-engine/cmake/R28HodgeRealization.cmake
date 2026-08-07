find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r28_hodge_store STATIC
  src/apparatus/host/hodge_realization_card_adapter.cpp
  src/apparatus/host/hodge_realization_store_adapter.cpp)
target_link_libraries(r28_hodge_store PRIVATE holonics::apparatus holonics_contract_options)

add_library(r28_hodge_executor STATIC
  src/apparatus/host/lean_checker_process.cpp
  src/cuda/executor/r28_hodge_realization_executor.cu
  src/cuda/executor/r28_hodge_realization_kernels.cu)
target_link_libraries(r28_hodge_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r28_hodge_device_deed
  src/apparatus/host/r28_hodge_realization_deed.cpp
  tests/model/r28_artifact.cpp
  tests/model/r28_atlas.cpp
  tests/model/r28_cases.cpp
  tests/model/r28_verify.cpp)
target_include_directories(r28_hodge_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r28_hodge_device_deed PRIVATE holonics::apparatus holonics_contract_options
  r28_hodge_store r28_hodge_executor CUDA::cudart)

add_executable(r28_hodge_host_conformance
  tests/conformance/r28_hodge_realization_host_conformance.cpp tests/model/r28_cases.cpp)
target_include_directories(r28_hodge_host_conformance PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r28_hodge_host_conformance
  PRIVATE holonics::event holonics_contract_options CUDA::cudart)

add_custom_target(r28_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r28_hodge_device_deed>
  DEPENDS r28_hodge_device_deed VERBATIM)

file(GLOB_RECURSE R28_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/*.hpp")
set(R28_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/r28_hodge_realization_kernels.cu")
set(R28_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r28_hodge_realization_kernels.ptx")
set(R28_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r28_hodge_realization_kernels.cubin")
set(R28_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/src/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R28_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R28_DEVICE_COMMON_FLAGS} --ptx
    "${R28_DEVICE_SOURCE}" -o "${R28_DEVICE_PTX}"
  DEPENDS "${R28_DEVICE_SOURCE}" ${R28_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R28_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R28_DEVICE_COMMON_FLAGS} --cubin
    "${R28_DEVICE_SOURCE}" -o "${R28_DEVICE_CUBIN}"
  DEPENDS "${R28_DEVICE_SOURCE}" ${R28_DEVICE_HEADERS} VERBATIM)
add_custom_target(r28_device_artifacts ALL DEPENDS ${R28_DEVICE_PTX} ${R28_DEVICE_CUBIN})

string(JOIN " " R28_DEVICE_FLAGS_RECEIPT ${R28_DEVICE_COMMON_FLAGS})
set(R28_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R28_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r28_hodge_realization_kernels.cu -o <BUILD>/generated/r28_hodge_realization_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R28_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r28_hodge_realization_kernels.cu -o <BUILD>/generated/r28_hodge_realization_kernels.cubin\n"
  "checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R28_GENERATED_HODGE_REALIZATION.olean <BUILD>/artifacts/R28_GENERATED_HODGE_REALIZATION.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts" "${PROJECT_BINARY_DIR}/receipts")
set(R28_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R28_HODGE_REALIZATION_DEED.txt")
set(R28_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R28_HODGE_REALIZATION_HANDOFF.rest")
set(R28_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R28_GENERATED_HODGE_REALIZATION.lean")
set(R28_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R28_GENERATED_HODGE_REALIZATION.olean")
set(R28_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R28_LEAN_STDOUT.txt")
set(R28_STDERR "${PROJECT_BINARY_DIR}/artifacts/R28_LEAN_STDERR.txt")
set(R28_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R28_HODGE_REALIZATION_ATLAS.tsv")
holonic_found(NAME r28.hodge_device_deed
  EXECUTABLE r28_hodge_device_deed
  COMMAND
    "${R28_DEED_ARTIFACT}" "${R27_FINAL_REST}" "${R28_FINAL_REST}"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R28_HODGE_REALIZATION.card" "${R28_SOURCE}"
    "${R28_OLEAN}" "${R28_STDOUT}" "${R28_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R28_ATLAS}")
holonic_found(NAME r28.hodge_host_conformance
  EXECUTABLE r28_hodge_host_conformance
  COMMAND
   )
add_test(NAME r28.forbidden_hodge_copy COMMAND "${CMAKE_COMMAND}"
  -DCOMPILER=${CMAKE_CXX_COMPILER}
  -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_hodge_realization_copy.cpp
  -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/src/include "-DEXPECTED_TEXT=use of deleted function"
  -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R28_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r28_hodge_device_deed>|${R28_DEVICE_PTX}|${R28_DEVICE_CUBIN}")
set(R28_DEVICE_PTX_LIST "${R28_DEVICE_PTX}")
set(R28_DEVICE_CUBIN_LIST "${R28_DEVICE_CUBIN}")
