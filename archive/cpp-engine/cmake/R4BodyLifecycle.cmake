find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(
  r4_body_lifecycle_executor STATIC
  src/cuda/executor/r4_adversarial_kernels.cu
  src/cuda/executor/r4_lifecycle_executor.cu
  src/cuda/executor/r4_lifecycle_kernels.cu)
target_link_libraries(
  r4_body_lifecycle_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(
  r4_body_lifecycle_device_deed
  src/apparatus/host/r4_body_lifecycle_deed.cpp
  tests/model/r4_artifact.cpp
  tests/model/r4_verify.cpp)
target_include_directories(r4_body_lifecycle_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r4_body_lifecycle_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r4_body_lifecycle_executor CUDA::cudart)

add_executable(
  r4_body_lifecycle_host_conformance
  tests/conformance/r4_body_host_conformance.cpp)
target_link_libraries(
  r4_body_lifecycle_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(
  r4_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r4_body_lifecycle_device_deed>
  DEPENDS r4_body_lifecycle_device_deed
  VERBATIM)

file(
  GLOB_RECURSE R4_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/*.hpp")
set(R4_LIFECYCLE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/r4_lifecycle_kernels.cu")
set(R4_ADVERSARIAL_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/r4_adversarial_kernels.cu")
set(R4_LIFECYCLE_PTX "${R0_GENERATED_DIRECTORY}/r4_lifecycle_kernels.ptx")
set(R4_LIFECYCLE_CUBIN "${R0_GENERATED_DIRECTORY}/r4_lifecycle_kernels.cubin")
set(R4_ADVERSARIAL_PTX "${R0_GENERATED_DIRECTORY}/r4_adversarial_kernels.ptx")
set(R4_ADVERSARIAL_CUBIN "${R0_GENERATED_DIRECTORY}/r4_adversarial_kernels.cubin")
set(R4_DEVICE_COMMON_FLAGS
    --std=c++20
    -O3
    --gpu-architecture=sm_89
    --fmad=false
    --Werror=all-warnings
    -I${PROJECT_SOURCE_DIR}/src/include
    -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
foreach(kind IN ITEMS LIFECYCLE ADVERSARIAL)
  add_custom_command(
    OUTPUT "${R4_${kind}_PTX}"
    COMMAND "${CMAKE_CUDA_COMPILER}" ${R4_DEVICE_COMMON_FLAGS} --ptx
      "${R4_${kind}_SOURCE}" -o "${R4_${kind}_PTX}"
    DEPENDS "${R4_${kind}_SOURCE}" ${R4_DEVICE_HEADERS}
    VERBATIM)
  add_custom_command(
    OUTPUT "${R4_${kind}_CUBIN}"
    COMMAND "${CMAKE_CUDA_COMPILER}" ${R4_DEVICE_COMMON_FLAGS} --cubin
      "${R4_${kind}_SOURCE}" -o "${R4_${kind}_CUBIN}"
    DEPENDS "${R4_${kind}_SOURCE}" ${R4_DEVICE_HEADERS}
    VERBATIM)
endforeach()
add_custom_target(r4_device_artifacts ALL DEPENDS
  ${R4_LIFECYCLE_PTX} ${R4_LIFECYCLE_CUBIN}
  ${R4_ADVERSARIAL_PTX} ${R4_ADVERSARIAL_CUBIN})

string(JOIN " " R4_DEVICE_FLAGS_RECEIPT ${R4_DEVICE_COMMON_FLAGS})
set(R4_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${R4_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r4_lifecycle_kernels.cu -o <BUILD>/generated/r4_lifecycle_kernels.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${R4_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r4_lifecycle_kernels.cu -o <BUILD>/generated/r4_lifecycle_kernels.cubin\n"
    "device_ptx=<CUDA_COMPILER> ${R4_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r4_adversarial_kernels.cu -o <BUILD>/generated/r4_adversarial_kernels.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${R4_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r4_adversarial_kernels.cu -o <BUILD>/generated/r4_adversarial_kernels.cubin\n")

set(R4_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R4_BODY_LIFECYCLE_DEED.txt")
holonic_found(NAME r4.body_lifecycle_device_deed
  EXECUTABLE r4_body_lifecycle_device_deed
  COMMAND
    "${R4_DEED_ARTIFACT}")
holonic_found(NAME r4.body_lifecycle_host_conformance
  EXECUTABLE r4_body_lifecycle_host_conformance
  COMMAND
   )
add_test(NAME r4.forbidden_body_lifecycle_copy
  COMMAND "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_body_lifecycle_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/src/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R4_EXTRA_ARTIFACTS
    "$<TARGET_FILE:r4_body_lifecycle_device_deed>|${R4_LIFECYCLE_PTX}|${R4_LIFECYCLE_CUBIN}|${R4_ADVERSARIAL_PTX}|${R4_ADVERSARIAL_CUBIN}")
set(R4_DEVICE_PTX "${R4_LIFECYCLE_PTX}|${R4_ADVERSARIAL_PTX}")
set(R4_DEVICE_CUBIN "${R4_LIFECYCLE_CUBIN}|${R4_ADVERSARIAL_CUBIN}")
