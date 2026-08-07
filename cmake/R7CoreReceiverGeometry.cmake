find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(
  r7_core_receiver_geometry_executor STATIC
  cuda/executor/r7_geometry_executor.cu
  cuda/executor/r7_geometry_kernels.cu)
target_link_libraries(
  r7_core_receiver_geometry_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(
  r7_core_receiver_geometry_device_deed
  apparatus/host/r7_core_receiver_geometry_deed.cpp
  tests/model/r6_cases.cpp
  tests/model/r6_oracle.cpp
  tests/model/r7_artifact.cpp
  tests/model/r7_cases.cpp
  tests/model/r7_oracle.cpp
  tests/model/r7_verify.cpp)
target_include_directories(
  r7_core_receiver_geometry_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r7_core_receiver_geometry_device_deed
  PRIVATE holonics::apparatus holonics_contract_options
    r7_core_receiver_geometry_executor CUDA::cudart)

add_executable(
  r7_core_receiver_geometry_host_conformance
  tests/conformance/r7_geometry_host_conformance.cpp
  tests/model/r6_cases.cpp
  tests/model/r6_oracle.cpp
  tests/model/r7_cases.cpp
  tests/model/r7_oracle.cpp)
target_include_directories(
  r7_core_receiver_geometry_host_conformance PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r7_core_receiver_geometry_host_conformance
  PRIVATE holonics::apparatus holonics_contract_options)

add_custom_target(
  r7_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r7_core_receiver_geometry_device_deed>
  DEPENDS r7_core_receiver_geometry_device_deed
  VERBATIM)

file(
  GLOB_RECURSE R7_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R7_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r7_geometry_kernels.cu")
set(R7_DEVICE_LAW "${PROJECT_SOURCE_DIR}/cuda/executor/r7_geometry_law.cuh")
set(R7_R6_DEVICE_LAW "${PROJECT_SOURCE_DIR}/cuda/executor/r6_weave_law.cuh")
set(R7_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r7_geometry_kernels.ptx")
set(R7_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r7_geometry_kernels.cubin")
set(R7_DEVICE_COMMON_FLAGS
    --std=c++20
    -O3
    --gpu-architecture=sm_89
    --fmad=false
    --Werror=all-warnings
    -I${PROJECT_SOURCE_DIR}/include
    -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(
  OUTPUT "${R7_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R7_DEVICE_COMMON_FLAGS} --ptx
    "${R7_DEVICE_SOURCE}" -o "${R7_DEVICE_PTX}"
  DEPENDS "${R7_DEVICE_SOURCE}" "${R7_DEVICE_LAW}" "${R7_R6_DEVICE_LAW}"
    ${R7_DEVICE_HEADERS}
  VERBATIM)
add_custom_command(
  OUTPUT "${R7_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R7_DEVICE_COMMON_FLAGS} --cubin
    "${R7_DEVICE_SOURCE}" -o "${R7_DEVICE_CUBIN}"
  DEPENDS "${R7_DEVICE_SOURCE}" "${R7_DEVICE_LAW}" "${R7_R6_DEVICE_LAW}"
    ${R7_DEVICE_HEADERS}
  VERBATIM)
add_custom_target(r7_device_artifacts ALL DEPENDS ${R7_DEVICE_PTX} ${R7_DEVICE_CUBIN})

string(JOIN " " R7_DEVICE_FLAGS_RECEIPT ${R7_DEVICE_COMMON_FLAGS})
set(R7_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${R7_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r7_geometry_kernels.cu -o <BUILD>/generated/r7_geometry_kernels.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${R7_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r7_geometry_kernels.cu -o <BUILD>/generated/r7_geometry_kernels.cubin\n")

set(R7_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R7_CORE_RECEIVER_GEOMETRY_DEED.txt")
holonic_found(NAME r7.core_receiver_geometry_device_deed
  EXECUTABLE r7_core_receiver_geometry_device_deed
  COMMAND
    "${R7_DEED_ARTIFACT}")
holonic_found(NAME r7.core_receiver_geometry_host_conformance
  EXECUTABLE r7_core_receiver_geometry_host_conformance
  COMMAND
   )
add_test(NAME r7.forbidden_receiver_geometry_copy
  COMMAND "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_receiver_geometry_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R7_EXTRA_ARTIFACTS
    "$<TARGET_FILE:r7_core_receiver_geometry_device_deed>|${R7_DEVICE_PTX}|${R7_DEVICE_CUBIN}")
