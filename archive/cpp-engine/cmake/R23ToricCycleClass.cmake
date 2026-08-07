find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r23_toric_cycle_store STATIC
  src/apparatus/host/toric_cycle_card_adapter.cpp
  src/apparatus/host/toric_cycle_store_adapter.cpp)
target_link_libraries(r23_toric_cycle_store
  PRIVATE holonics::apparatus holonics_contract_options)

add_library(r23_toric_cycle_executor STATIC
  src/apparatus/host/lean_checker_process.cpp
  src/cuda/executor/r23_toric_cycle_executor.cu
  src/cuda/executor/r23_toric_cycle_kernels.cu
  src/cuda/executor/r23_toric_cycle_probe.cu)
target_link_libraries(r23_toric_cycle_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r23_toric_cycle_device_deed
  src/apparatus/host/r23_toric_cycle_deed.cpp
  tests/model/r22_cases.cpp
  tests/model/r23_artifact.cpp
  tests/model/r23_cases.cpp
  tests/model/r23_verify.cpp)
target_include_directories(r23_toric_cycle_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r23_toric_cycle_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r23_toric_cycle_store
    r23_toric_cycle_executor CUDA::cudart)

add_executable(r23_toric_cycle_host_conformance
  tests/conformance/r23_toric_cycle_host_conformance.cpp
  tests/model/r22_cases.cpp
  tests/model/r23_cases.cpp)
target_include_directories(r23_toric_cycle_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r23_toric_cycle_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r23_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r23_toric_cycle_device_deed>
  DEPENDS r23_toric_cycle_device_deed VERBATIM)

file(GLOB_RECURSE R23_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/*.hpp")
set(R23_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/r23_toric_cycle_kernels.cu")
set(R23_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r23_toric_cycle_kernels.ptx")
set(R23_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r23_toric_cycle_kernels.cubin")
set(R23_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/src/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R23_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R23_DEVICE_COMMON_FLAGS} --ptx
    "${R23_DEVICE_SOURCE}" -o "${R23_DEVICE_PTX}"
  DEPENDS "${R23_DEVICE_SOURCE}" ${R23_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R23_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R23_DEVICE_COMMON_FLAGS} --cubin
    "${R23_DEVICE_SOURCE}" -o "${R23_DEVICE_CUBIN}"
  DEPENDS "${R23_DEVICE_SOURCE}" ${R23_DEVICE_HEADERS} VERBATIM)
add_custom_target(r23_device_artifacts ALL DEPENDS ${R23_DEVICE_PTX} ${R23_DEVICE_CUBIN})

string(JOIN " " R23_DEVICE_FLAGS_RECEIPT ${R23_DEVICE_COMMON_FLAGS})
set(R23_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R23_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r23_toric_cycle_kernels.cu -o <BUILD>/generated/r23_toric_cycle_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R23_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r23_toric_cycle_kernels.cu -o <BUILD>/generated/r23_toric_cycle_kernels.cubin\n"
  "checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R23_GENERATED_TORIC_CYCLE.olean <BUILD>/artifacts/R23_GENERATED_TORIC_CYCLE.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts" "${PROJECT_BINARY_DIR}/receipts")
set(R23_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R23_TORIC_CYCLE_DEED.txt")
set(R23_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R23_TORIC_CYCLE_HANDOFF.rest")
set(R23_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R23_GENERATED_TORIC_CYCLE.lean")
set(R23_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R23_GENERATED_TORIC_CYCLE.olean")
set(R23_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R23_LEAN_STDOUT.txt")
set(R23_STDERR "${PROJECT_BINARY_DIR}/artifacts/R23_LEAN_STDERR.txt")
set(R23_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R23_TORIC_CYCLE_ATLAS.tsv")
holonic_found(NAME r23.toric_cycle_device_deed
  EXECUTABLE r23_toric_cycle_device_deed
  COMMAND
    "${R23_DEED_ARTIFACT}" "${R22_FINAL_REST}" "${R23_FINAL_REST}"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R23_TORIC_CYCLE.card" "${R23_SOURCE}"
    "${R23_OLEAN}" "${R23_STDOUT}" "${R23_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R23_ATLAS}")
holonic_found(NAME r23.toric_cycle_host_conformance
  EXECUTABLE r23_toric_cycle_host_conformance
  COMMAND
   )
add_test(NAME r23.forbidden_toric_cycle_copy
  COMMAND "${CMAKE_COMMAND}" -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_toric_cycle_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/src/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R23_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r23_toric_cycle_device_deed>|${R23_DEVICE_PTX}|${R23_DEVICE_CUBIN}")
set(R23_DEVICE_PTX_LIST "${R23_DEVICE_PTX}")
set(R23_DEVICE_CUBIN_LIST "${R23_DEVICE_CUBIN}")
