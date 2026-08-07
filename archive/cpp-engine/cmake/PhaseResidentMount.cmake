find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(resident_ecology_executor STATIC src/cuda/executor/resident_ecology_executor.cu)
target_link_libraries(
  resident_ecology_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(
  resident_mount_deed
  src/apparatus/host/resident_mount_deed.cpp
  tests/model/cost_cases.cpp)
target_include_directories(resident_mount_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  resident_mount_deed
  PRIVATE holonics::apparatus holonics_contract_options resident_ecology_executor
          CUDA::cudart)

set(RESIDENT_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/resident_ecology_executor.cu")
file(
  GLOB RESIDENT_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/apparatus/*.hpp"
  "${PROJECT_SOURCE_DIR}/src/include/holonics/organ/*.hpp"
  "${PROJECT_SOURCE_DIR}/src/include/holonics/structure/*.hpp")
set(RESIDENT_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/resident_ecology_executor.ptx")
set(RESIDENT_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/resident_ecology_executor.cubin")
set(RESIDENT_DEVICE_COMMON_FLAGS
    --std=c++20
    -O3
    --gpu-architecture=sm_89
    --fmad=false
    --Werror=all-warnings
    -I${PROJECT_SOURCE_DIR}/src/include
    -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)

add_custom_command(
  OUTPUT "${RESIDENT_DEVICE_PTX}"
  COMMAND
    "${CMAKE_CUDA_COMPILER}" ${RESIDENT_DEVICE_COMMON_FLAGS} --ptx
    "${RESIDENT_DEVICE_SOURCE}" -o "${RESIDENT_DEVICE_PTX}"
  DEPENDS "${RESIDENT_DEVICE_SOURCE}" ${RESIDENT_DEVICE_HEADERS}
  VERBATIM)
add_custom_command(
  OUTPUT "${RESIDENT_DEVICE_CUBIN}"
  COMMAND
    "${CMAKE_CUDA_COMPILER}" ${RESIDENT_DEVICE_COMMON_FLAGS} --cubin
    "${RESIDENT_DEVICE_SOURCE}" -o "${RESIDENT_DEVICE_CUBIN}"
  DEPENDS "${RESIDENT_DEVICE_SOURCE}" ${RESIDENT_DEVICE_HEADERS}
  VERBATIM)
add_custom_target(
  resident_device_artifacts ALL
  DEPENDS "${RESIDENT_DEVICE_PTX}" "${RESIDENT_DEVICE_CUBIN}")

string(JOIN " " RESIDENT_DEVICE_FLAGS_RECEIPT ${RESIDENT_DEVICE_COMMON_FLAGS})
set(RESIDENT_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${RESIDENT_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/resident_ecology_executor.cu -o <BUILD>/generated/resident_ecology_executor.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${RESIDENT_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/resident_ecology_executor.cu -o <BUILD>/generated/resident_ecology_executor.cubin\n")

set(RESIDENT_EXTRA_ARTIFACTS
    "$<TARGET_FILE:resident_mount_deed>|${RESIDENT_DEVICE_PTX}|${RESIDENT_DEVICE_CUBIN}")
set(RESIDENT_DEVICE_PTX_LIST "${RESIDENT_DEVICE_PTX}")
set(RESIDENT_DEVICE_CUBIN_LIST "${RESIDENT_DEVICE_CUBIN}")

set(RESIDENT_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/PHASE_7_RESIDENT_MOUNT_DEED.txt")
holonic_found(NAME phase_resident.resident_mount_deed
  EXECUTABLE resident_mount_deed
  COMMAND
    "${RESIDENT_DEED_ARTIFACT}")
