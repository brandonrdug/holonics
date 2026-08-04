find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r15_theorem_rest_store STATIC
  apparatus/host/theorem_rest_store_adapter.cpp)
target_link_libraries(r15_theorem_rest_store
  PRIVATE holonics::apparatus holonics_contract_options)

add_library(r15_return_conditioning_executor STATIC
  cuda/executor/r15_return_conditioning_executor.cu
  cuda/executor/r15_return_conditioning_kernels.cu)
target_link_libraries(r15_return_conditioning_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r15_return_conditioning_device_deed
  apparatus/host/r15_return_conditioned_morphology_deed.cpp
  tests/model/r15_artifact.cpp
  tests/model/r15_cases.cpp
  tests/model/r15_verify.cpp)
target_include_directories(r15_return_conditioning_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r15_return_conditioning_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r15_theorem_rest_store
    r15_return_conditioning_executor CUDA::cudart)

add_executable(r15_return_conditioning_host_conformance
  tests/conformance/r15_return_conditioning_host_conformance.cpp
  tests/model/r15_cases.cpp)
target_include_directories(r15_return_conditioning_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r15_return_conditioning_host_conformance
  PRIVATE holonics::event holonics_contract_options r15_theorem_rest_store)

add_custom_target(r15_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r15_return_conditioning_device_deed>
  DEPENDS r15_return_conditioning_device_deed VERBATIM)

file(GLOB_RECURSE R15_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R15_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r15_return_conditioning_kernels.cu")
set(R15_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r15_return_conditioning_kernels.ptx")
set(R15_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r15_return_conditioning_kernels.cubin")
set(R15_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R15_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R15_DEVICE_COMMON_FLAGS} --ptx
    "${R15_DEVICE_SOURCE}" -o "${R15_DEVICE_PTX}"
  DEPENDS "${R15_DEVICE_SOURCE}" ${R15_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R15_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R15_DEVICE_COMMON_FLAGS} --cubin
    "${R15_DEVICE_SOURCE}" -o "${R15_DEVICE_CUBIN}"
  DEPENDS "${R15_DEVICE_SOURCE}" ${R15_DEVICE_HEADERS} VERBATIM)
add_custom_target(r15_device_artifacts ALL DEPENDS ${R15_DEVICE_PTX} ${R15_DEVICE_CUBIN})

string(JOIN " " R15_DEVICE_FLAGS_RECEIPT ${R15_DEVICE_COMMON_FLAGS})
set(R15_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R15_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r15_return_conditioning_kernels.cu -o <BUILD>/generated/r15_return_conditioning_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R15_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r15_return_conditioning_kernels.cu -o <BUILD>/generated/r15_return_conditioning_kernels.cubin\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts")
set(R15_DEED_ARTIFACT
  "${PROJECT_BINARY_DIR}/receipts/R15_RETURN_CONDITIONED_MORPHOLOGY_DEED.txt")
set(R15_HANDOFF_REST "${PROJECT_BINARY_DIR}/artifacts/R15_THEOREM_PRODUCTION_HANDOFF.rest")
set(R15_DEED_B_SETUP "${PROJECT_BINARY_DIR}/artifacts/R15_DEED_B_SETUP.bin")
add_test(NAME r15.return_conditioned_morphology_device_deed
  COMMAND r15_return_conditioning_device_deed "${R15_DEED_ARTIFACT}"
    "${R14_HANDOFF_REST}" "${R15_HANDOFF_REST}" "${R15_DEED_B_SETUP}")
set_tests_properties(r15.return_conditioned_morphology_device_deed PROPERTIES
  DEPENDS "r14.first_theorem_production_device_deed")
add_test(NAME r15.return_conditioning_host_conformance
  COMMAND r15_return_conditioning_host_conformance "${R14_HANDOFF_REST}")
set_tests_properties(r15.return_conditioning_host_conformance PROPERTIES
  DEPENDS "r14.first_theorem_production_device_deed")

set(R15_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r15_return_conditioning_device_deed>|${R15_DEVICE_PTX}|${R15_DEVICE_CUBIN}")
set(R15_DEVICE_PTX_LIST "${R15_DEVICE_PTX}")
set(R15_DEVICE_CUBIN_LIST "${R15_DEVICE_CUBIN}")
