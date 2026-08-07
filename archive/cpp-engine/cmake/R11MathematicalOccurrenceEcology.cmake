find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r11_mathematical_ecology_executor STATIC
  src/cuda/executor/r11_mathematical_ecology_executor.cu
  src/cuda/executor/r11_mathematical_ecology_kernels.cu)
target_link_libraries(r11_mathematical_ecology_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r11_mathematical_ecology_device_deed
  src/apparatus/host/r11_mathematical_occurrence_ecology_deed.cpp
  src/apparatus/host/mathematical_source_adapter.cpp
  tests/model/r11_artifact.cpp
  tests/model/r11_cases.cpp
  tests/model/r11_oracle.cpp
  tests/model/r11_verify.cpp)
target_include_directories(r11_mathematical_ecology_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r11_mathematical_ecology_device_deed
  PRIVATE holonics::apparatus holonics_contract_options
    r11_mathematical_ecology_executor CUDA::cudart)

add_executable(r11_mathematical_ecology_host_conformance
  tests/conformance/r11_mathematical_ecology_host_conformance.cpp
  tests/model/r11_cases.cpp
  tests/model/r11_oracle.cpp)
target_include_directories(r11_mathematical_ecology_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r11_mathematical_ecology_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r11_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r11_mathematical_ecology_device_deed>
  DEPENDS r11_mathematical_ecology_device_deed VERBATIM)

file(GLOB_RECURSE R11_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/*.hpp")
set(R11_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/r11_mathematical_ecology_kernels.cu")
set(R11_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r11_mathematical_ecology_kernels.ptx")
set(R11_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r11_mathematical_ecology_kernels.cubin")
set(R11_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/src/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R11_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R11_DEVICE_COMMON_FLAGS} --ptx
    "${R11_DEVICE_SOURCE}" -o "${R11_DEVICE_PTX}"
  DEPENDS "${R11_DEVICE_SOURCE}" ${R11_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R11_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R11_DEVICE_COMMON_FLAGS} --cubin
    "${R11_DEVICE_SOURCE}" -o "${R11_DEVICE_CUBIN}"
  DEPENDS "${R11_DEVICE_SOURCE}" ${R11_DEVICE_HEADERS} VERBATIM)
add_custom_target(r11_device_artifacts ALL DEPENDS ${R11_DEVICE_PTX} ${R11_DEVICE_CUBIN})

string(JOIN " " R11_DEVICE_FLAGS_RECEIPT ${R11_DEVICE_COMMON_FLAGS})
set(R11_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R11_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r11_mathematical_ecology_kernels.cu -o <BUILD>/generated/r11_mathematical_ecology_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R11_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r11_mathematical_ecology_kernels.cu -o <BUILD>/generated/r11_mathematical_ecology_kernels.cubin\n")

set(R11_DEED_ARTIFACT
  "${PROJECT_BINARY_DIR}/receipts/R11_MATHEMATICAL_OCCURRENCE_ECOLOGY_DEED.txt")
holonic_found(NAME r11.mathematical_ecology_device_deed
  EXECUTABLE r11_mathematical_ecology_device_deed
  COMMAND
    "${R11_DEED_ARTIFACT}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/ElementaryHolonics/Algorithm/Transition.lean"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/ElementaryHolonics/Algorithm/Rebase.lean"
    "${PROJECT_BINARY_DIR}/r11_relocated_formal")
holonic_found(NAME r11.mathematical_ecology_host_conformance
  EXECUTABLE r11_mathematical_ecology_host_conformance
  COMMAND
   )
add_test(NAME r11.forbidden_mathematical_ecology_copy
  COMMAND "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_mathematical_ecology_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/src/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R11_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r11_mathematical_ecology_device_deed>|${R11_DEVICE_PTX}|${R11_DEVICE_CUBIN}")
