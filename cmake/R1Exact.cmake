find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r1_exact_executor STATIC cuda/executor/r1_exact_executor.cu)
target_link_libraries(
  r1_exact_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(
  r1_exact_device_deed
  apparatus/host/r1_exact_deed.cpp
  tests/model/r1_artifact.cpp
  tests/model/r1_cases.cpp
  tests/model/r1_oracle.cpp)
target_include_directories(r1_exact_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r1_exact_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r1_exact_executor CUDA::cudart)

add_executable(
  r1_exact_host_conformance
  tests/conformance/r1_exact_host_conformance.cpp
  tests/model/r1_cases.cpp
  tests/model/r1_oracle.cpp)
target_include_directories(r1_exact_host_conformance PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r1_exact_host_conformance
  PRIVATE holonics::exact holonics_contract_options)

add_custom_target(
  r1_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r1_exact_device_deed>
  DEPENDS r1_exact_device_deed
  VERBATIM)

set(R1_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r1_exact_executor.cu")
file(
  GLOB R1_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/apparatus/*.hpp"
  "${PROJECT_SOURCE_DIR}/include/holonics/current/*.hpp"
  "${PROJECT_SOURCE_DIR}/include/holonics/exact/*.hpp")
set(R1_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r1_exact_executor.ptx")
set(R1_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r1_exact_executor.cubin")
set(R1_DEVICE_COMMON_FLAGS
    --std=c++20
    -O3
    --gpu-architecture=sm_89
    --fmad=false
    --Werror=all-warnings
    -I${PROJECT_SOURCE_DIR}/include
    -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)

add_custom_command(
  OUTPUT "${R1_DEVICE_PTX}"
  COMMAND
    "${CMAKE_CUDA_COMPILER}" ${R1_DEVICE_COMMON_FLAGS} --ptx
    "${R1_DEVICE_SOURCE}" -o "${R1_DEVICE_PTX}"
  DEPENDS "${R1_DEVICE_SOURCE}" ${R1_DEVICE_HEADERS}
  VERBATIM)
add_custom_command(
  OUTPUT "${R1_DEVICE_CUBIN}"
  COMMAND
    "${CMAKE_CUDA_COMPILER}" ${R1_DEVICE_COMMON_FLAGS} --cubin
    "${R1_DEVICE_SOURCE}" -o "${R1_DEVICE_CUBIN}"
  DEPENDS "${R1_DEVICE_SOURCE}" ${R1_DEVICE_HEADERS}
  VERBATIM)
add_custom_target(r1_device_artifacts ALL DEPENDS "${R1_DEVICE_PTX}" "${R1_DEVICE_CUBIN}")

string(JOIN " " R1_DEVICE_FLAGS_RECEIPT ${R1_DEVICE_COMMON_FLAGS})
set(R1_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${R1_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r1_exact_executor.cu -o <BUILD>/generated/r1_exact_executor.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${R1_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r1_exact_executor.cu -o <BUILD>/generated/r1_exact_executor.cubin\n")

set(R1_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R1_EXACT_DEED.txt")
holonic_found(NAME r1.exact_device_deed
  EXECUTABLE r1_exact_device_deed
  COMMAND
    "${R1_DEED_ARTIFACT}")
holonic_found(NAME r1.exact_host_conformance
  EXECUTABLE r1_exact_host_conformance
  COMMAND
   )
