find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(spine_executor STATIC cuda/executor/spine_executor.cu)
target_link_libraries(
  spine_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(
  spine_device_deed
  apparatus/host/spine_deed.cpp
  tests/model/spine_cases.cpp)
target_include_directories(spine_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  spine_device_deed
  PRIVATE holonics::apparatus holonics_contract_options spine_executor CUDA::cudart)

add_executable(
  spine_host_conformance
  tests/conformance/spine_host_conformance.cpp
  tests/model/spine_cases.cpp)
target_include_directories(spine_host_conformance PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  spine_host_conformance
  PRIVATE holonics::apparatus holonics_contract_options)

set(SPINE_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/spine_executor.cu")
file(
  GLOB SPINE_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/apparatus/*.hpp"
  "${PROJECT_SOURCE_DIR}/include/holonics/current/*.hpp"
  "${PROJECT_SOURCE_DIR}/include/holonics/exact/*.hpp")
set(SPINE_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/spine_executor.ptx")
set(SPINE_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/spine_executor.cubin")
set(SPINE_DEVICE_COMMON_FLAGS
    --std=c++20
    -O3
    --gpu-architecture=sm_89
    --fmad=false
    --Werror=all-warnings
    -I${PROJECT_SOURCE_DIR}/include
    -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)

add_custom_command(
  OUTPUT "${SPINE_DEVICE_PTX}"
  COMMAND
    "${CMAKE_CUDA_COMPILER}" ${SPINE_DEVICE_COMMON_FLAGS} --ptx
    "${SPINE_DEVICE_SOURCE}" -o "${SPINE_DEVICE_PTX}"
  DEPENDS "${SPINE_DEVICE_SOURCE}" ${SPINE_DEVICE_HEADERS}
  VERBATIM)
add_custom_command(
  OUTPUT "${SPINE_DEVICE_CUBIN}"
  COMMAND
    "${CMAKE_CUDA_COMPILER}" ${SPINE_DEVICE_COMMON_FLAGS} --cubin
    "${SPINE_DEVICE_SOURCE}" -o "${SPINE_DEVICE_CUBIN}"
  DEPENDS "${SPINE_DEVICE_SOURCE}" ${SPINE_DEVICE_HEADERS}
  VERBATIM)
add_custom_target(
  spine_device_artifacts ALL
  DEPENDS "${SPINE_DEVICE_PTX}" "${SPINE_DEVICE_CUBIN}")

string(JOIN " " SPINE_DEVICE_FLAGS_RECEIPT ${SPINE_DEVICE_COMMON_FLAGS})
set(SPINE_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${SPINE_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/spine_executor.cu -o <BUILD>/generated/spine_executor.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${SPINE_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/spine_executor.cu -o <BUILD>/generated/spine_executor.cubin\n")

set(SPINE_EXTRA_ARTIFACTS
    "$<TARGET_FILE:spine_device_deed>|${SPINE_DEVICE_PTX}|${SPINE_DEVICE_CUBIN}")
set(SPINE_DEVICE_PTX_LIST "${SPINE_DEVICE_PTX}")
set(SPINE_DEVICE_CUBIN_LIST "${SPINE_DEVICE_CUBIN}")

set(SPINE_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/MOVEMENT_A_SPINE_DEED.txt")
add_test(
  NAME phase_spine.spine_device_deed
  COMMAND spine_device_deed "${SPINE_DEED_ARTIFACT}")
add_test(NAME phase_spine.spine_host_conformance COMMAND spine_host_conformance)
