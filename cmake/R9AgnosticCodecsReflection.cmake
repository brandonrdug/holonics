find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(
  r9_agnostic_codecs_reflection_executor STATIC
  cuda/executor/r9_codec_executor.cu
  cuda/executor/r9_codec_kernels.cu)
target_link_libraries(
  r9_agnostic_codecs_reflection_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(
  r9_agnostic_codecs_reflection_device_deed
  apparatus/host/r9_agnostic_codecs_reflection_deed.cpp
  apparatus/host/codec_store_adapter.cpp
  tests/model/r9_artifact.cpp
  tests/model/r9_cases.cpp
  tests/model/r9_oracle.cpp
  tests/model/r9_verify.cpp)
target_include_directories(
  r9_agnostic_codecs_reflection_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r9_agnostic_codecs_reflection_device_deed
  PRIVATE holonics::apparatus holonics_contract_options
    r9_agnostic_codecs_reflection_executor CUDA::cudart)

add_executable(
  r9_agnostic_codecs_reflection_host_conformance
  apparatus/host/codec_store_adapter.cpp
  tests/conformance/r9_codec_host_conformance.cpp
  tests/model/r9_cases.cpp
  tests/model/r9_oracle.cpp)
target_include_directories(
  r9_agnostic_codecs_reflection_host_conformance PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(
  r9_agnostic_codecs_reflection_host_conformance
  PRIVATE holonics::event holonics::codec holonics_contract_options)

add_custom_target(
  r9_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded
    $<TARGET_FILE:r9_agnostic_codecs_reflection_device_deed>
  DEPENDS r9_agnostic_codecs_reflection_device_deed
  VERBATIM)

file(
  GLOB_RECURSE R9_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R9_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r9_codec_kernels.cu")
set(R9_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r9_codec_kernels.ptx")
set(R9_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r9_codec_kernels.cubin")
set(R9_DEVICE_COMMON_FLAGS
    --std=c++20
    -O3
    --gpu-architecture=sm_89
    --fmad=false
    --Werror=all-warnings
    -I${PROJECT_SOURCE_DIR}/include
    -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(
  OUTPUT "${R9_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R9_DEVICE_COMMON_FLAGS} --ptx
    "${R9_DEVICE_SOURCE}" -o "${R9_DEVICE_PTX}"
  DEPENDS "${R9_DEVICE_SOURCE}" ${R9_DEVICE_HEADERS}
  VERBATIM)
add_custom_command(
  OUTPUT "${R9_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R9_DEVICE_COMMON_FLAGS} --cubin
    "${R9_DEVICE_SOURCE}" -o "${R9_DEVICE_CUBIN}"
  DEPENDS "${R9_DEVICE_SOURCE}" ${R9_DEVICE_HEADERS}
  VERBATIM)
add_custom_target(r9_device_artifacts ALL DEPENDS ${R9_DEVICE_PTX} ${R9_DEVICE_CUBIN})

string(JOIN " " R9_DEVICE_FLAGS_RECEIPT ${R9_DEVICE_COMMON_FLAGS})
set(R9_DECLARED_COMMANDS
    "device_ptx=<CUDA_COMPILER> ${R9_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r9_codec_kernels.cu -o <BUILD>/generated/r9_codec_kernels.ptx\n"
    "device_cubin=<CUDA_COMPILER> ${R9_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r9_codec_kernels.cu -o <BUILD>/generated/r9_codec_kernels.cubin\n")

set(R9_CODEC_FIXTURE "${PROJECT_SOURCE_DIR}/tests/fixtures/r9_reflective_codec.hcodec")
set(R9_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R9_AGNOSTIC_CODECS_REFLECTION_DEED.txt")
holonic_found(NAME r9.agnostic_codecs_reflection_device_deed
  EXECUTABLE r9_agnostic_codecs_reflection_device_deed
  COMMAND
    "${R9_DEED_ARTIFACT}" "${R9_CODEC_FIXTURE}" "${PROJECT_BINARY_DIR}/r9-relocated-device")
holonic_found(NAME r9.agnostic_codecs_reflection_host_conformance
  EXECUTABLE r9_agnostic_codecs_reflection_host_conformance
  COMMAND
    "${R9_CODEC_FIXTURE}" "${PROJECT_BINARY_DIR}/r9-relocated-host")
add_test(NAME r9.forbidden_reflective_codec_copy
  COMMAND "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_reflective_codec_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R9_EXTRA_ARTIFACTS
    "$<TARGET_FILE:r9_agnostic_codecs_reflection_device_deed>|${R9_DEVICE_PTX}|${R9_DEVICE_CUBIN}")
