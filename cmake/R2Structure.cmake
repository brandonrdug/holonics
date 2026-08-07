find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r2_structure_executor STATIC cuda/executor/r2_structure_executor.cu)
target_link_libraries(
  r2_structure_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(
  r2_structure_device_deed
  apparatus/host/r2_structure_deed.cpp
  tests/model/r2_artifact.cpp
  tests/model/r2_cases.cpp
  tests/model/r2_verify.cpp)
target_include_directories(r2_structure_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r2_structure_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r2_structure_executor CUDA::cudart)

add_executable(
  r2_structure_host_conformance
  tests/conformance/r2_structure_host_conformance.cpp
  tests/model/r2_cases.cpp
  tests/model/r2_verify.cpp)
target_include_directories(r2_structure_host_conformance PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r2_structure_host_conformance
  PRIVATE holonics::structure holonics_contract_options)

add_custom_target(
  r2_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r2_structure_device_deed>
  DEPENDS r2_structure_device_deed
  VERBATIM)

set(R2_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r2_structure_executor.cu")
file(
  GLOB R2_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/apparatus/*.hpp"
  "${PROJECT_SOURCE_DIR}/include/holonics/current/*.hpp"
  "${PROJECT_SOURCE_DIR}/include/holonics/exact/*.hpp"
  "${PROJECT_SOURCE_DIR}/include/holonics/structure/*.hpp")
set(R2_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r2_structure_executor.ptx")
set(R2_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r2_structure_executor.cubin")
set(R2_DEVICE_COMMON_FLAGS
    --std=c++20
    -O3
    --gpu-architecture=sm_89
    --fmad=false
    --Werror=all-warnings
    -I${PROJECT_SOURCE_DIR}/include
    -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)

add_custom_command(
  OUTPUT "${R2_DEVICE_PTX}"
  COMMAND
    "${CMAKE_CUDA_COMPILER}" ${R2_DEVICE_COMMON_FLAGS} --ptx
    "${R2_DEVICE_SOURCE}" -o "${R2_DEVICE_PTX}"
  DEPENDS "${R2_DEVICE_SOURCE}" ${R2_DEVICE_HEADERS}
  VERBATIM)
add_custom_command(
  OUTPUT "${R2_DEVICE_CUBIN}"
  COMMAND
    "${CMAKE_CUDA_COMPILER}" ${R2_DEVICE_COMMON_FLAGS} --cubin
    "${R2_DEVICE_SOURCE}" -o "${R2_DEVICE_CUBIN}"
  DEPENDS "${R2_DEVICE_SOURCE}" ${R2_DEVICE_HEADERS}
  VERBATIM)
add_custom_target(r2_device_artifacts ALL DEPENDS "${R2_DEVICE_PTX}" "${R2_DEVICE_CUBIN}")

string(JOIN " " R2_DEVICE_FLAGS_RECEIPT ${R2_DEVICE_COMMON_FLAGS})
set(R2_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${R2_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r2_structure_executor.cu -o <BUILD>/generated/r2_structure_executor.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${R2_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r2_structure_executor.cu -o <BUILD>/generated/r2_structure_executor.cubin\n")

set(R2_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R2_STRUCTURE_DEED.txt")
holonic_found(NAME r2.structure_device_deed
  EXECUTABLE r2_structure_device_deed
  COMMAND
    "${R2_DEED_ARTIFACT}")
holonic_found(NAME r2.structure_host_conformance
  EXECUTABLE r2_structure_host_conformance
  COMMAND
   )
add_test(
  NAME r2.forbidden_structure_copy
  COMMAND
    "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_structure_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")
