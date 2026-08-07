find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(text_material_mount STATIC src/cuda/executor/text_material_mount.cu)
target_link_libraries(
  text_material_mount
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(text_mount_deed src/apparatus/host/text_mount_deed.cpp)
target_link_libraries(
  text_mount_deed
  PRIVATE holonics::apparatus holonics_contract_options text_material_mount
          CUDA::cudart)

set(TEXT_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/text_material_mount.cu")
file(
  GLOB TEXT_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/apparatus/*.hpp"
  "${PROJECT_SOURCE_DIR}/src/include/holonics/codec/text*.hpp"
  "${PROJECT_SOURCE_DIR}/src/include/holonics/event/text*.hpp"
  "${PROJECT_SOURCE_DIR}/src/include/holonics/organ/*.hpp"
  "${PROJECT_SOURCE_DIR}/src/cuda/executor/text_mount*.cuh")
set(TEXT_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/text_material_mount.ptx")
set(TEXT_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/text_material_mount.cubin")
set(TEXT_DEVICE_COMMON_FLAGS
    --std=c++20
    -O3
    --gpu-architecture=sm_89
    --fmad=false
    --Werror=all-warnings
    -I${PROJECT_SOURCE_DIR}/src/include
    -I${PROJECT_SOURCE_DIR}/src/cuda/executor
    -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)

add_custom_command(
  OUTPUT "${TEXT_DEVICE_PTX}"
  COMMAND
    "${CMAKE_CUDA_COMPILER}" ${TEXT_DEVICE_COMMON_FLAGS} --ptx
    "${TEXT_DEVICE_SOURCE}" -o "${TEXT_DEVICE_PTX}"
  DEPENDS "${TEXT_DEVICE_SOURCE}" ${TEXT_DEVICE_HEADERS}
  VERBATIM)
add_custom_command(
  OUTPUT "${TEXT_DEVICE_CUBIN}"
  COMMAND
    "${CMAKE_CUDA_COMPILER}" ${TEXT_DEVICE_COMMON_FLAGS} --cubin
    "${TEXT_DEVICE_SOURCE}" -o "${TEXT_DEVICE_CUBIN}"
  DEPENDS "${TEXT_DEVICE_SOURCE}" ${TEXT_DEVICE_HEADERS}
  VERBATIM)
add_custom_target(
  text_device_artifacts ALL
  DEPENDS "${TEXT_DEVICE_PTX}" "${TEXT_DEVICE_CUBIN}")

string(JOIN " " TEXT_DEVICE_FLAGS_RECEIPT ${TEXT_DEVICE_COMMON_FLAGS})
set(TEXT_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${TEXT_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/text_material_mount.cu -o <BUILD>/generated/text_material_mount.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${TEXT_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/text_material_mount.cu -o <BUILD>/generated/text_material_mount.cubin\n")

set(TEXT_EXTRA_ARTIFACTS
    "$<TARGET_FILE:text_mount_deed>|${TEXT_DEVICE_PTX}|${TEXT_DEVICE_CUBIN}")
set(TEXT_DEVICE_PTX_LIST "${TEXT_DEVICE_PTX}")
set(TEXT_DEVICE_CUBIN_LIST "${TEXT_DEVICE_CUBIN}")

set(TEXT_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/PHASE_7_BROAD_MOUNT_DEED.txt")
holonic_found(NAME phase_text.text_mount_deed
  EXECUTABLE text_mount_deed
  COMMAND
    "${PROJECT_SOURCE_DIR}" "${TEXT_DEED_ARTIFACT}")
