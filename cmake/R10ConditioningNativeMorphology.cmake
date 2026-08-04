find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r10_conditioning_executor STATIC
  cuda/executor/r10_conditioning_executor.cu
  cuda/executor/r10_conditioning_kernels.cu)
target_link_libraries(r10_conditioning_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r10_conditioning_device_deed
  apparatus/host/r10_conditioning_native_morphology_deed.cpp
  tests/model/r10_artifact.cpp
  tests/model/r10_cases.cpp
  tests/model/r10_oracle.cpp
  tests/model/r10_verify.cpp)
target_include_directories(r10_conditioning_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r10_conditioning_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r10_conditioning_executor CUDA::cudart)

add_executable(r10_conditioning_host_conformance
  tests/conformance/r10_conditioning_host_conformance.cpp
  tests/model/r10_cases.cpp
  tests/model/r10_oracle.cpp)
target_include_directories(r10_conditioning_host_conformance PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r10_conditioning_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r10_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r10_conditioning_device_deed>
  DEPENDS r10_conditioning_device_deed VERBATIM)

file(GLOB_RECURSE R10_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R10_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r10_conditioning_kernels.cu")
set(R10_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r10_conditioning_kernels.ptx")
set(R10_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r10_conditioning_kernels.cubin")
set(R10_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R10_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R10_DEVICE_COMMON_FLAGS} --ptx
    "${R10_DEVICE_SOURCE}" -o "${R10_DEVICE_PTX}"
  DEPENDS "${R10_DEVICE_SOURCE}" ${R10_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R10_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R10_DEVICE_COMMON_FLAGS} --cubin
    "${R10_DEVICE_SOURCE}" -o "${R10_DEVICE_CUBIN}"
  DEPENDS "${R10_DEVICE_SOURCE}" ${R10_DEVICE_HEADERS} VERBATIM)
add_custom_target(r10_device_artifacts ALL DEPENDS ${R10_DEVICE_PTX} ${R10_DEVICE_CUBIN})

string(JOIN " " R10_DEVICE_FLAGS_RECEIPT ${R10_DEVICE_COMMON_FLAGS})
set(R10_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R10_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r10_conditioning_kernels.cu -o <BUILD>/generated/r10_conditioning_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R10_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r10_conditioning_kernels.cu -o <BUILD>/generated/r10_conditioning_kernels.cubin\n")

set(R10_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R10_CONDITIONING_NATIVE_MORPHOLOGY_DEED.txt")
add_test(NAME r10.conditioning_device_deed
  COMMAND r10_conditioning_device_deed "${R10_DEED_ARTIFACT}")
add_test(NAME r10.conditioning_host_conformance COMMAND r10_conditioning_host_conformance)
add_test(NAME r10.forbidden_conditioned_organ_copy
  COMMAND "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_conditioned_organ_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R10_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r10_conditioning_device_deed>|${R10_DEVICE_PTX}|${R10_DEVICE_CUBIN}")
