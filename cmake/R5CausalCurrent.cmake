find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(
  r5_causal_current_executor STATIC
  cuda/executor/r5_current_executor.cu
  cuda/executor/r5_current_kernels.cu)
target_link_libraries(
  r5_causal_current_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(
  r5_causal_current_device_deed
  apparatus/host/r5_causal_current_deed.cpp
  tests/model/r5_artifact.cpp
  tests/model/r5_cases.cpp
  tests/model/r5_oracle.cpp
  tests/model/r5_verify.cpp)
target_include_directories(r5_causal_current_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r5_causal_current_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r5_causal_current_executor CUDA::cudart)

add_executable(
  r5_causal_current_host_conformance
  tests/conformance/r5_current_host_conformance.cpp
  tests/model/r5_cases.cpp
  tests/model/r5_oracle.cpp)
target_include_directories(r5_causal_current_host_conformance PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r5_causal_current_host_conformance
  PRIVATE holonics::current holonics_contract_options)

add_custom_target(
  r5_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r5_causal_current_device_deed>
  DEPENDS r5_causal_current_device_deed
  VERBATIM)

file(
  GLOB_RECURSE R5_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R5_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r5_current_kernels.cu")
set(R5_DEVICE_FRONT "${PROJECT_SOURCE_DIR}/cuda/executor/r5_current_front.cuh")
set(R5_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r5_current_kernels.ptx")
set(R5_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r5_current_kernels.cubin")
set(R5_DEVICE_COMMON_FLAGS
    --std=c++20
    -O3
    --gpu-architecture=sm_89
    --fmad=false
    --Werror=all-warnings
    -I${PROJECT_SOURCE_DIR}/include
    -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(
  OUTPUT "${R5_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R5_DEVICE_COMMON_FLAGS} --ptx
    "${R5_DEVICE_SOURCE}" -o "${R5_DEVICE_PTX}"
  DEPENDS "${R5_DEVICE_SOURCE}" "${R5_DEVICE_FRONT}" ${R5_DEVICE_HEADERS}
  VERBATIM)
add_custom_command(
  OUTPUT "${R5_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R5_DEVICE_COMMON_FLAGS} --cubin
    "${R5_DEVICE_SOURCE}" -o "${R5_DEVICE_CUBIN}"
  DEPENDS "${R5_DEVICE_SOURCE}" "${R5_DEVICE_FRONT}" ${R5_DEVICE_HEADERS}
  VERBATIM)
add_custom_target(r5_device_artifacts ALL DEPENDS ${R5_DEVICE_PTX} ${R5_DEVICE_CUBIN})

string(JOIN " " R5_DEVICE_FLAGS_RECEIPT ${R5_DEVICE_COMMON_FLAGS})
set(R5_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${R5_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r5_current_kernels.cu -o <BUILD>/generated/r5_current_kernels.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${R5_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r5_current_kernels.cu -o <BUILD>/generated/r5_current_kernels.cubin\n")

set(R5_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R5_CAUSAL_CURRENT_DEED.txt")
add_test(NAME r5.causal_current_device_deed
  COMMAND r5_causal_current_device_deed "${R5_DEED_ARTIFACT}")
add_test(NAME r5.causal_current_host_conformance COMMAND r5_causal_current_host_conformance)
add_test(NAME r5.forbidden_causal_current_copy
  COMMAND "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_causal_current_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R5_EXTRA_ARTIFACTS
    "$<TARGET_FILE:r5_causal_current_device_deed>|${R5_DEVICE_PTX}|${R5_DEVICE_CUBIN}")
