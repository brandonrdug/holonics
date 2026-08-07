find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(
  r8_stateful_boundary_condensation_executor STATIC
  src/cuda/executor/r8_condensation_executor.cu
  src/cuda/executor/r8_condensation_kernels.cu)
target_link_libraries(
  r8_stateful_boundary_condensation_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(
  r8_stateful_boundary_condensation_device_deed
  src/apparatus/host/r8_stateful_boundary_condensation_deed.cpp
  tests/model/r8_artifact.cpp
  tests/model/r8_cases.cpp
  tests/model/r8_oracle.cpp
  tests/model/r8_verify.cpp)
target_include_directories(
  r8_stateful_boundary_condensation_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r8_stateful_boundary_condensation_device_deed
  PRIVATE holonics::apparatus holonics_contract_options
    r8_stateful_boundary_condensation_executor CUDA::cudart)

add_executable(
  r8_stateful_boundary_condensation_host_conformance
  tests/conformance/r8_condensation_host_conformance.cpp
  tests/model/r8_cases.cpp
  tests/model/r8_oracle.cpp)
target_include_directories(
  r8_stateful_boundary_condensation_host_conformance PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r8_stateful_boundary_condensation_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(
  r8_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded
    $<TARGET_FILE:r8_stateful_boundary_condensation_device_deed>
  DEPENDS r8_stateful_boundary_condensation_device_deed
  VERBATIM)

file(
  GLOB_RECURSE R8_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/*.hpp")
set(R8_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/r8_condensation_kernels.cu")
set(R8_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r8_condensation_kernels.ptx")
set(R8_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r8_condensation_kernels.cubin")
set(R8_DEVICE_COMMON_FLAGS
    --std=c++20
    -O3
    --gpu-architecture=sm_89
    --fmad=false
    --Werror=all-warnings
    -I${PROJECT_SOURCE_DIR}/src/include
    -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(
  OUTPUT "${R8_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R8_DEVICE_COMMON_FLAGS} --ptx
    "${R8_DEVICE_SOURCE}" -o "${R8_DEVICE_PTX}"
  DEPENDS "${R8_DEVICE_SOURCE}" ${R8_DEVICE_HEADERS}
  VERBATIM)
add_custom_command(
  OUTPUT "${R8_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R8_DEVICE_COMMON_FLAGS} --cubin
    "${R8_DEVICE_SOURCE}" -o "${R8_DEVICE_CUBIN}"
  DEPENDS "${R8_DEVICE_SOURCE}" ${R8_DEVICE_HEADERS}
  VERBATIM)
add_custom_target(r8_device_artifacts ALL DEPENDS ${R8_DEVICE_PTX} ${R8_DEVICE_CUBIN})

string(JOIN " " R8_DEVICE_FLAGS_RECEIPT ${R8_DEVICE_COMMON_FLAGS})
set(R8_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${R8_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r8_condensation_kernels.cu -o <BUILD>/generated/r8_condensation_kernels.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${R8_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r8_condensation_kernels.cu -o <BUILD>/generated/r8_condensation_kernels.cubin\n")

set(R8_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R8_STATEFUL_BOUNDARY_CONDENSATION_DEED.txt")
holonic_found(NAME r8.stateful_boundary_condensation_device_deed
  EXECUTABLE r8_stateful_boundary_condensation_device_deed
  COMMAND
    "${R8_DEED_ARTIFACT}")
holonic_found(NAME r8.stateful_boundary_condensation_host_conformance
  EXECUTABLE r8_stateful_boundary_condensation_host_conformance
  COMMAND
   )
add_test(NAME r8.forbidden_condensation_copy
  COMMAND "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_condensation_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/src/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R8_EXTRA_ARTIFACTS
    "$<TARGET_FILE:r8_stateful_boundary_condensation_device_deed>|${R8_DEVICE_PTX}|${R8_DEVICE_CUBIN}")
