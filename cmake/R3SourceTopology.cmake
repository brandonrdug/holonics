find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(
  r3_source_topology_executor STATIC
  cuda/executor/r3_admission_kernels.cu
  cuda/executor/r3_source_executor.cu
  cuda/executor/r3_source_kernels.cu
  cuda/executor/r3_navigation_kernels.cu)
target_link_libraries(
  r3_source_topology_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(
  r3_source_topology_device_deed
  apparatus/host/r3_source_topology_deed.cpp
  apparatus/host/source_store_adapter.cpp
  tests/model/r3_artifact.cpp
  tests/model/r3_verify.cpp)
target_include_directories(r3_source_topology_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r3_source_topology_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r3_source_topology_executor CUDA::cudart)

add_executable(
  r3_source_topology_host_conformance
  apparatus/host/source_store_adapter.cpp
  tests/conformance/r3_source_host_conformance.cpp
  tests/model/r3_verify.cpp)
target_include_directories(
  r3_source_topology_host_conformance PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r3_source_topology_host_conformance
  PRIVATE holonics::apparatus holonics_contract_options)

add_custom_target(
  r3_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r3_source_topology_device_deed>
  DEPENDS r3_source_topology_device_deed
  VERBATIM)

file(
  GLOB_RECURSE R3_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R3_FOUNDATION_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r3_source_kernels.cu")
set(R3_NAVIGATION_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r3_navigation_kernels.cu")
set(R3_ADMISSION_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r3_admission_kernels.cu")
set(R3_FOUNDATION_PTX "${R0_GENERATED_DIRECTORY}/r3_source_kernels.ptx")
set(R3_FOUNDATION_CUBIN "${R0_GENERATED_DIRECTORY}/r3_source_kernels.cubin")
set(R3_NAVIGATION_PTX "${R0_GENERATED_DIRECTORY}/r3_navigation_kernels.ptx")
set(R3_NAVIGATION_CUBIN "${R0_GENERATED_DIRECTORY}/r3_navigation_kernels.cubin")
set(R3_ADMISSION_PTX "${R0_GENERATED_DIRECTORY}/r3_admission_kernels.ptx")
set(R3_ADMISSION_CUBIN "${R0_GENERATED_DIRECTORY}/r3_admission_kernels.cubin")
set(R3_DEVICE_COMMON_FLAGS
    --std=c++20
    -O3
    --gpu-architecture=sm_89
    --fmad=false
    --Werror=all-warnings
    -I${PROJECT_SOURCE_DIR}/include
    -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)

foreach(kind IN ITEMS FOUNDATION NAVIGATION ADMISSION)
  add_custom_command(
    OUTPUT "${R3_${kind}_PTX}"
    COMMAND "${CMAKE_CUDA_COMPILER}" ${R3_DEVICE_COMMON_FLAGS} --ptx
      "${R3_${kind}_SOURCE}" -o "${R3_${kind}_PTX}"
    DEPENDS "${R3_${kind}_SOURCE}" ${R3_DEVICE_HEADERS}
    VERBATIM)
  add_custom_command(
    OUTPUT "${R3_${kind}_CUBIN}"
    COMMAND "${CMAKE_CUDA_COMPILER}" ${R3_DEVICE_COMMON_FLAGS} --cubin
      "${R3_${kind}_SOURCE}" -o "${R3_${kind}_CUBIN}"
    DEPENDS "${R3_${kind}_SOURCE}" ${R3_DEVICE_HEADERS}
    VERBATIM)
endforeach()
add_custom_target(
  r3_device_artifacts ALL
  DEPENDS ${R3_FOUNDATION_PTX} ${R3_FOUNDATION_CUBIN}
    ${R3_NAVIGATION_PTX} ${R3_NAVIGATION_CUBIN}
    ${R3_ADMISSION_PTX} ${R3_ADMISSION_CUBIN})

string(JOIN " " R3_DEVICE_FLAGS_RECEIPT ${R3_DEVICE_COMMON_FLAGS})
set(R3_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${R3_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r3_source_kernels.cu -o <BUILD>/generated/r3_source_kernels.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${R3_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r3_source_kernels.cu -o <BUILD>/generated/r3_source_kernels.cubin\n"
    "device_ptx=<CUDA_COMPILER> ${R3_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r3_navigation_kernels.cu -o <BUILD>/generated/r3_navigation_kernels.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${R3_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r3_navigation_kernels.cu -o <BUILD>/generated/r3_navigation_kernels.cubin\n"
    "device_ptx=<CUDA_COMPILER> ${R3_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r3_admission_kernels.cu -o <BUILD>/generated/r3_admission_kernels.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${R3_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r3_admission_kernels.cu -o <BUILD>/generated/r3_admission_kernels.cubin\n")

set(R3_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R3_SOURCE_TOPOLOGY_DEED.txt")
set(R3_SOURCE_PATHS
    "${PROJECT_SOURCE_DIR}/CONSTRUCTION_STATE.md"
    "${PROJECT_SOURCE_DIR}/papers/source/synopsis/README.md"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/ElementaryHolonics/Foundation/Receiver.lean")
add_test(
  NAME r3.source_topology_device_deed
  COMMAND r3_source_topology_device_deed "${R3_DEED_ARTIFACT}" ${R3_SOURCE_PATHS}
    "${PROJECT_BINARY_DIR}/r3-relocated-device")
add_test(
  NAME r3.source_topology_host_conformance
  COMMAND r3_source_topology_host_conformance ${R3_SOURCE_PATHS}
    "${PROJECT_BINARY_DIR}/r3-relocated-host")
add_test(
  NAME r3.forbidden_source_environment_copy
  COMMAND "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_source_environment_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R3_EXTRA_ARTIFACTS
    "$<TARGET_FILE:r3_source_topology_device_deed>|${R3_FOUNDATION_PTX}|${R3_FOUNDATION_CUBIN}|${R3_NAVIGATION_PTX}|${R3_NAVIGATION_CUBIN}|${R3_ADMISSION_PTX}|${R3_ADMISSION_CUBIN}")
set(R3_DEVICE_PTX "${R3_FOUNDATION_PTX}|${R3_NAVIGATION_PTX}|${R3_ADMISSION_PTX}")
set(R3_DEVICE_CUBIN "${R3_FOUNDATION_CUBIN}|${R3_NAVIGATION_CUBIN}|${R3_ADMISSION_CUBIN}")
