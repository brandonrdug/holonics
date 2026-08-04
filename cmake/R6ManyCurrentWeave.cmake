find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(
  r6_many_current_weave_executor STATIC
  cuda/executor/r6_weave_executor.cu
  cuda/executor/r6_weave_kernels.cu)
target_link_libraries(
  r6_many_current_weave_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(
  r6_many_current_weave_device_deed
  apparatus/host/r6_many_current_weave_deed.cpp
  tests/model/r6_artifact.cpp
  tests/model/r6_cases.cpp
  tests/model/r6_oracle.cpp
  tests/model/r6_verify.cpp)
target_include_directories(
  r6_many_current_weave_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r6_many_current_weave_device_deed
  PRIVATE holonics::apparatus holonics_contract_options
    r6_many_current_weave_executor CUDA::cudart)

add_executable(
  r6_many_current_weave_host_conformance
  tests/conformance/r6_weave_host_conformance.cpp
  tests/model/r6_cases.cpp
  tests/model/r6_oracle.cpp)
target_include_directories(
  r6_many_current_weave_host_conformance PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r6_many_current_weave_host_conformance
  PRIVATE holonics::current holonics_contract_options)

add_custom_target(
  r6_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r6_many_current_weave_device_deed>
  DEPENDS r6_many_current_weave_device_deed
  VERBATIM)

file(
  GLOB_RECURSE R6_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R6_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r6_weave_kernels.cu")
set(R6_DEVICE_LAW "${PROJECT_SOURCE_DIR}/cuda/executor/r6_weave_law.cuh")
set(R6_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r6_weave_kernels.ptx")
set(R6_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r6_weave_kernels.cubin")
set(R6_DEVICE_COMMON_FLAGS
    --std=c++20
    -O3
    --gpu-architecture=sm_89
    --fmad=false
    --Werror=all-warnings
    -I${PROJECT_SOURCE_DIR}/include
    -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(
  OUTPUT "${R6_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R6_DEVICE_COMMON_FLAGS} --ptx
    "${R6_DEVICE_SOURCE}" -o "${R6_DEVICE_PTX}"
  DEPENDS "${R6_DEVICE_SOURCE}" "${R6_DEVICE_LAW}" ${R6_DEVICE_HEADERS}
  VERBATIM)
add_custom_command(
  OUTPUT "${R6_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R6_DEVICE_COMMON_FLAGS} --cubin
    "${R6_DEVICE_SOURCE}" -o "${R6_DEVICE_CUBIN}"
  DEPENDS "${R6_DEVICE_SOURCE}" "${R6_DEVICE_LAW}" ${R6_DEVICE_HEADERS}
  VERBATIM)
add_custom_target(r6_device_artifacts ALL DEPENDS ${R6_DEVICE_PTX} ${R6_DEVICE_CUBIN})

string(JOIN " " R6_DEVICE_FLAGS_RECEIPT ${R6_DEVICE_COMMON_FLAGS})
set(R6_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${R6_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r6_weave_kernels.cu -o <BUILD>/generated/r6_weave_kernels.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${R6_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r6_weave_kernels.cu -o <BUILD>/generated/r6_weave_kernels.cubin\n")

set(R6_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R6_MANY_CURRENT_WEAVE_DEED.txt")
add_test(NAME r6.many_current_weave_device_deed
  COMMAND r6_many_current_weave_device_deed "${R6_DEED_ARTIFACT}")
add_test(NAME r6.many_current_weave_host_conformance
  COMMAND r6_many_current_weave_host_conformance)
add_test(NAME r6.forbidden_weave_copy
  COMMAND "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_weave_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R6_EXTRA_ARTIFACTS
    "$<TARGET_FILE:r6_many_current_weave_device_deed>|${R6_DEVICE_PTX}|${R6_DEVICE_CUBIN}")
