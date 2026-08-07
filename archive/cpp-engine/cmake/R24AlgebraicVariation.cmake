find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r24_algebraic_variation_store STATIC
  src/apparatus/host/algebraic_variation_card_adapter.cpp
  src/apparatus/host/algebraic_variation_store_adapter.cpp)
target_link_libraries(r24_algebraic_variation_store
  PRIVATE holonics::apparatus holonics_contract_options)

add_library(r24_algebraic_variation_executor STATIC
  src/apparatus/host/lean_checker_process.cpp
  src/cuda/executor/r24_algebraic_variation_executor.cu
  src/cuda/executor/r24_algebraic_variation_kernels.cu
  src/cuda/executor/r24_algebraic_variation_probe.cu)
target_link_libraries(r24_algebraic_variation_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r24_algebraic_variation_device_deed
  src/apparatus/host/r24_algebraic_variation_deed.cpp
  tests/model/r22_cases.cpp
  tests/model/r23_cases.cpp
  tests/model/r24_artifact.cpp
  tests/model/r24_cases.cpp
  tests/model/r24_verify.cpp)
target_include_directories(r24_algebraic_variation_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r24_algebraic_variation_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r24_algebraic_variation_store
    r24_algebraic_variation_executor CUDA::cudart)

add_executable(r24_algebraic_variation_host_conformance
  tests/conformance/r24_algebraic_variation_host_conformance.cpp)
target_link_libraries(r24_algebraic_variation_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r24_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r24_algebraic_variation_device_deed>
  DEPENDS r24_algebraic_variation_device_deed VERBATIM)

file(GLOB_RECURSE R24_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/*.hpp")
set(R24_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/r24_algebraic_variation_kernels.cu")
set(R24_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r24_algebraic_variation_kernels.ptx")
set(R24_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r24_algebraic_variation_kernels.cubin")
set(R24_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/src/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R24_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R24_DEVICE_COMMON_FLAGS} --ptx
    "${R24_DEVICE_SOURCE}" -o "${R24_DEVICE_PTX}"
  DEPENDS "${R24_DEVICE_SOURCE}" ${R24_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R24_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R24_DEVICE_COMMON_FLAGS} --cubin
    "${R24_DEVICE_SOURCE}" -o "${R24_DEVICE_CUBIN}"
  DEPENDS "${R24_DEVICE_SOURCE}" ${R24_DEVICE_HEADERS} VERBATIM)
add_custom_target(r24_device_artifacts ALL DEPENDS ${R24_DEVICE_PTX} ${R24_DEVICE_CUBIN})

string(JOIN " " R24_DEVICE_FLAGS_RECEIPT ${R24_DEVICE_COMMON_FLAGS})
set(R24_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R24_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r24_algebraic_variation_kernels.cu -o <BUILD>/generated/r24_algebraic_variation_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R24_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r24_algebraic_variation_kernels.cu -o <BUILD>/generated/r24_algebraic_variation_kernels.cubin\n"
  "checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R24_GENERATED_ALGEBRAIC_VARIATION.olean <BUILD>/artifacts/R24_GENERATED_ALGEBRAIC_VARIATION.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts" "${PROJECT_BINARY_DIR}/receipts")
set(R24_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R24_ALGEBRAIC_VARIATION_DEED.txt")
set(R24_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R24_ALGEBRAIC_VARIATION_HANDOFF.rest")
set(R24_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R24_GENERATED_ALGEBRAIC_VARIATION.lean")
set(R24_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R24_GENERATED_ALGEBRAIC_VARIATION.olean")
set(R24_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R24_LEAN_STDOUT.txt")
set(R24_STDERR "${PROJECT_BINARY_DIR}/artifacts/R24_LEAN_STDERR.txt")
set(R24_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R24_ALGEBRAIC_VARIATION_ATLAS.tsv")
holonic_found(NAME r24.algebraic_variation_device_deed
  EXECUTABLE r24_algebraic_variation_device_deed
  COMMAND
    "${R24_DEED_ARTIFACT}" "${R23_FINAL_REST}" "${R24_FINAL_REST}"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R24_ALGEBRAIC_VARIATION.card" "${R24_SOURCE}"
    "${R24_OLEAN}" "${R24_STDOUT}" "${R24_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R24_ATLAS}")
holonic_found(NAME r24.algebraic_variation_host_conformance
  EXECUTABLE r24_algebraic_variation_host_conformance
  COMMAND
   )
add_test(NAME r24.forbidden_algebraic_variation_copy
  COMMAND "${CMAKE_COMMAND}" -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_algebraic_variation_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/src/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R24_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r24_algebraic_variation_device_deed>|${R24_DEVICE_PTX}|${R24_DEVICE_CUBIN}")
set(R24_DEVICE_PTX_LIST "${R24_DEVICE_PTX}")
set(R24_DEVICE_CUBIN_LIST "${R24_DEVICE_CUBIN}")
