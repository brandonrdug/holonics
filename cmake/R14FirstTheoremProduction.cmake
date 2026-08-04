find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r14_theorem_production_executor STATIC
  apparatus/host/lean_checker_process.cpp
  cuda/executor/r14_theorem_production_executor.cu
  cuda/executor/r14_theorem_production_kernels.cu)
target_link_libraries(r14_theorem_production_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r14_theorem_production_device_deed
  apparatus/host/r14_first_theorem_production_deed.cpp
  tests/model/r14_artifact.cpp
  tests/model/r14_cases.cpp
  tests/model/r14_verify.cpp)
target_include_directories(r14_theorem_production_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r14_theorem_production_device_deed
  PRIVATE holonics::apparatus holonics_contract_options
    r14_theorem_production_executor CUDA::cudart)

add_executable(r14_theorem_production_host_conformance
  tests/conformance/r14_theorem_production_host_conformance.cpp
  tests/model/r14_cases.cpp)
target_include_directories(r14_theorem_production_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r14_theorem_production_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r14_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r14_theorem_production_device_deed>
  DEPENDS r14_theorem_production_device_deed VERBATIM)

file(GLOB_RECURSE R14_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R14_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r14_theorem_production_kernels.cu")
set(R14_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r14_theorem_production_kernels.ptx")
set(R14_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r14_theorem_production_kernels.cubin")
set(R14_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R14_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R14_DEVICE_COMMON_FLAGS} --ptx
    "${R14_DEVICE_SOURCE}" -o "${R14_DEVICE_PTX}"
  DEPENDS "${R14_DEVICE_SOURCE}" ${R14_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R14_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R14_DEVICE_COMMON_FLAGS} --cubin
    "${R14_DEVICE_SOURCE}" -o "${R14_DEVICE_CUBIN}"
  DEPENDS "${R14_DEVICE_SOURCE}" ${R14_DEVICE_HEADERS} VERBATIM)
add_custom_target(r14_device_artifacts ALL DEPENDS ${R14_DEVICE_PTX} ${R14_DEVICE_CUBIN})

string(JOIN " " R14_DEVICE_FLAGS_RECEIPT ${R14_DEVICE_COMMON_FLAGS})
set(R14_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R14_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r14_theorem_production_kernels.cu -o <BUILD>/generated/r14_theorem_production_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R14_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r14_theorem_production_kernels.cu -o <BUILD>/generated/r14_theorem_production_kernels.cubin\n"
  "exterior_checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R14_GENERATED_TRACE_COMPOSITION.olean <BUILD>/artifacts/R14_GENERATED_TRACE_COMPOSITION.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts")
set(R14_DEED_ARTIFACT
  "${PROJECT_BINARY_DIR}/receipts/R14_FIRST_THEOREM_PRODUCTION_DEED.txt")
set(R14_HANDOFF_REST "${PROJECT_BINARY_DIR}/artifacts/R14_THEOREM_PRODUCTION_HANDOFF.rest")
set(R14_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R14_GENERATED_TRACE_COMPOSITION.lean")
set(R14_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R14_GENERATED_TRACE_COMPOSITION.olean")
set(R14_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R14_LEAN_STDOUT.txt")
set(R14_STDERR "${PROJECT_BINARY_DIR}/artifacts/R14_LEAN_STDERR.txt")
add_test(NAME r14.first_theorem_production_device_deed
  COMMAND r14_theorem_production_device_deed "${R14_DEED_ARTIFACT}"
    "${R14_HANDOFF_REST}" "${R14_SOURCE}" "${R14_OLEAN}" "${R14_STDOUT}" "${R14_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts")
set_tests_properties(r14.first_theorem_production_device_deed PROPERTIES
  DEPENDS "r13.lean_checker_device_deed")
add_test(NAME r14.theorem_production_host_conformance
  COMMAND r14_theorem_production_host_conformance)
add_test(NAME r14.forbidden_theorem_production_copy
  COMMAND "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_theorem_production_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R14_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r14_theorem_production_device_deed>|${R14_DEVICE_PTX}|${R14_DEVICE_CUBIN}")
set(R14_DEVICE_PTX_LIST "${R14_DEVICE_PTX}")
set(R14_DEVICE_CUBIN_LIST "${R14_DEVICE_CUBIN}")
