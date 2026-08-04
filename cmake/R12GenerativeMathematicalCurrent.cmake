find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r12_generative_math_executor STATIC
  cuda/executor/r12_generative_math_executor.cu
  cuda/executor/r12_generative_math_kernels.cu)
target_link_libraries(r12_generative_math_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r12_generative_math_device_deed
  apparatus/host/r12_generative_mathematical_current_deed.cpp
  tests/model/r12_artifact.cpp
  tests/model/r12_cases.cpp
  tests/model/r12_oracle.cpp
  tests/model/r12_verify.cpp)
target_include_directories(r12_generative_math_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r12_generative_math_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r12_generative_math_executor CUDA::cudart)

add_executable(r12_generative_math_host_conformance
  tests/conformance/r12_generative_math_host_conformance.cpp
  tests/model/r12_cases.cpp
  tests/model/r12_oracle.cpp
  tests/model/r12_verify.cpp)
target_include_directories(r12_generative_math_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r12_generative_math_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r12_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r12_generative_math_device_deed>
  DEPENDS r12_generative_math_device_deed VERBATIM)

file(GLOB_RECURSE R12_DEVICE_HEADERS CONFIGURE_DEPENDS "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R12_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r12_generative_math_kernels.cu")
set(R12_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r12_generative_math_kernels.ptx")
set(R12_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r12_generative_math_kernels.cubin")
set(R12_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R12_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R12_DEVICE_COMMON_FLAGS} --ptx
    "${R12_DEVICE_SOURCE}" -o "${R12_DEVICE_PTX}"
  DEPENDS "${R12_DEVICE_SOURCE}" ${R12_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R12_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R12_DEVICE_COMMON_FLAGS} --cubin
    "${R12_DEVICE_SOURCE}" -o "${R12_DEVICE_CUBIN}"
  DEPENDS "${R12_DEVICE_SOURCE}" ${R12_DEVICE_HEADERS} VERBATIM)
add_custom_target(r12_device_artifacts ALL DEPENDS ${R12_DEVICE_PTX} ${R12_DEVICE_CUBIN})

string(JOIN " " R12_DEVICE_FLAGS_RECEIPT ${R12_DEVICE_COMMON_FLAGS})
set(R12_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R12_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r12_generative_math_kernels.cu -o <BUILD>/generated/r12_generative_math_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R12_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r12_generative_math_kernels.cu -o <BUILD>/generated/r12_generative_math_kernels.cubin\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts")
set(R12_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R12_GENERATIVE_MATHEMATICAL_CURRENT_DEED.txt")
set(R12_GENERATED_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R12_GENERATED_REBASE_REVERSE.lean")
set(R12_GENERATED_EXPLANATION "${PROJECT_BINARY_DIR}/artifacts/R12_GENERATED_REBASE_REVERSE.txt")
add_test(NAME r12.generative_math_device_deed
  COMMAND r12_generative_math_device_deed "${R12_DEED_ARTIFACT}"
    "${R12_GENERATED_SOURCE}" "${R12_GENERATED_EXPLANATION}")
add_test(NAME r12.generative_math_host_conformance COMMAND r12_generative_math_host_conformance)
add_test(NAME r12.forbidden_generative_math_current_copy
  COMMAND "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_generative_math_current_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R12_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r12_generative_math_device_deed>|${R12_DEVICE_PTX}|${R12_DEVICE_CUBIN}")
