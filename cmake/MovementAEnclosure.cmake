find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(enclosure_executor STATIC cuda/executor/enclosure_executor.cu)
target_link_libraries(
  enclosure_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(
  enclosure_device_deed
  apparatus/host/enclosure_deed.cpp
  tests/model/enclosure_cases.cpp)
target_include_directories(enclosure_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  enclosure_device_deed
  PRIVATE holonics::apparatus holonics_contract_options enclosure_executor CUDA::cudart)

add_executable(
  enclosure_host_conformance
  tests/conformance/enclosure_host_conformance.cpp
  tests/model/enclosure_cases.cpp)
target_include_directories(enclosure_host_conformance PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  enclosure_host_conformance
  PRIVATE holonics::exact holonics_contract_options)

set(ENCLOSURE_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/enclosure_executor.cu")
file(
  GLOB ENCLOSURE_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/apparatus/*.hpp"
  "${PROJECT_SOURCE_DIR}/include/holonics/current/*.hpp"
  "${PROJECT_SOURCE_DIR}/include/holonics/exact/*.hpp")
set(ENCLOSURE_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/enclosure_executor.ptx")
set(ENCLOSURE_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/enclosure_executor.cubin")
set(ENCLOSURE_DEVICE_COMMON_FLAGS
    --std=c++20
    -O3
    --gpu-architecture=sm_89
    --fmad=false
    --Werror=all-warnings
    -I${PROJECT_SOURCE_DIR}/include
    -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)

add_custom_command(
  OUTPUT "${ENCLOSURE_DEVICE_PTX}"
  COMMAND
    "${CMAKE_CUDA_COMPILER}" ${ENCLOSURE_DEVICE_COMMON_FLAGS} --ptx
    "${ENCLOSURE_DEVICE_SOURCE}" -o "${ENCLOSURE_DEVICE_PTX}"
  DEPENDS "${ENCLOSURE_DEVICE_SOURCE}" ${ENCLOSURE_DEVICE_HEADERS}
  VERBATIM)
add_custom_command(
  OUTPUT "${ENCLOSURE_DEVICE_CUBIN}"
  COMMAND
    "${CMAKE_CUDA_COMPILER}" ${ENCLOSURE_DEVICE_COMMON_FLAGS} --cubin
    "${ENCLOSURE_DEVICE_SOURCE}" -o "${ENCLOSURE_DEVICE_CUBIN}"
  DEPENDS "${ENCLOSURE_DEVICE_SOURCE}" ${ENCLOSURE_DEVICE_HEADERS}
  VERBATIM)
add_custom_target(
  enclosure_device_artifacts ALL
  DEPENDS "${ENCLOSURE_DEVICE_PTX}" "${ENCLOSURE_DEVICE_CUBIN}")

string(JOIN " " ENCLOSURE_DEVICE_FLAGS_RECEIPT ${ENCLOSURE_DEVICE_COMMON_FLAGS})
set(ENCLOSURE_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${ENCLOSURE_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/enclosure_executor.cu -o <BUILD>/generated/enclosure_executor.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${ENCLOSURE_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/enclosure_executor.cu -o <BUILD>/generated/enclosure_executor.cubin\n")

set(ENCLOSURE_EXTRA_ARTIFACTS
    "$<TARGET_FILE:enclosure_device_deed>|${ENCLOSURE_DEVICE_PTX}|${ENCLOSURE_DEVICE_CUBIN}")
set(ENCLOSURE_DEVICE_PTX_LIST "${ENCLOSURE_DEVICE_PTX}")
set(ENCLOSURE_DEVICE_CUBIN_LIST "${ENCLOSURE_DEVICE_CUBIN}")

set(ENCLOSURE_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/MOVEMENT_A_ENCLOSURE_DEED.txt")
holonic_found(NAME movement_a.enclosure_device_deed
  EXECUTABLE enclosure_device_deed
  COMMAND
    "${ENCLOSURE_DEED_ARTIFACT}")
holonic_found(NAME movement_a.enclosure_host_conformance
  EXECUTABLE enclosure_host_conformance
  COMMAND
   )
