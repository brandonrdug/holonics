find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r16_terminal_bundle_store STATIC
  apparatus/host/terminal_bundle_store_adapter.cpp)
target_link_libraries(r16_terminal_bundle_store
  PRIVATE holonics::apparatus holonics_contract_options)

add_library(r16_terminal_theorem_executor STATIC
  apparatus/host/lean_checker_process.cpp
  apparatus/host/returned_theorem_checker_process.cpp
  cuda/executor/r16_terminal_theorem_executor.cu
  cuda/executor/r16_terminal_theorem_kernels.cu)
target_link_libraries(r16_terminal_theorem_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r16_two_theorem_conversational_device_deed
  apparatus/host/r16_two_theorem_conversational_deed.cpp
  tests/model/r16_artifact.cpp
  tests/model/r16_cases.cpp
  tests/model/r16_verify.cpp)
target_include_directories(r16_two_theorem_conversational_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r16_two_theorem_conversational_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r15_theorem_rest_store
    r16_terminal_bundle_store r16_terminal_theorem_executor CUDA::cudart)

add_executable(r16_terminal_theorem_host_conformance
  tests/conformance/r16_terminal_theorem_host_conformance.cpp
  tests/model/r16_cases.cpp)
target_include_directories(r16_terminal_theorem_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r16_terminal_theorem_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r16_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded
    $<TARGET_FILE:r16_two_theorem_conversational_device_deed>
  DEPENDS r16_two_theorem_conversational_device_deed VERBATIM)

file(GLOB_RECURSE R16_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R16_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r16_terminal_theorem_kernels.cu")
set(R16_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r16_terminal_theorem_kernels.ptx")
set(R16_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r16_terminal_theorem_kernels.cubin")
set(R16_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R16_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R16_DEVICE_COMMON_FLAGS} --ptx
    "${R16_DEVICE_SOURCE}" -o "${R16_DEVICE_PTX}"
  DEPENDS "${R16_DEVICE_SOURCE}" ${R16_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R16_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R16_DEVICE_COMMON_FLAGS} --cubin
    "${R16_DEVICE_SOURCE}" -o "${R16_DEVICE_CUBIN}"
  DEPENDS "${R16_DEVICE_SOURCE}" ${R16_DEVICE_HEADERS} VERBATIM)
add_custom_target(r16_device_artifacts ALL DEPENDS ${R16_DEVICE_PTX} ${R16_DEVICE_CUBIN})

string(JOIN " " R16_DEVICE_FLAGS_RECEIPT ${R16_DEVICE_COMMON_FLAGS})
set(R16_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R16_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r16_terminal_theorem_kernels.cu -o <BUILD>/generated/r16_terminal_theorem_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R16_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r16_terminal_theorem_kernels.cu -o <BUILD>/generated/r16_terminal_theorem_kernels.cubin\n"
  "exterior_checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R16_GENERATED_TRACE_THREE.olean <BUILD>/artifacts/R16_GENERATED_TRACE_THREE.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts")
set(R16_DEED_ARTIFACT
  "${PROJECT_BINARY_DIR}/receipts/R16_TWO_THEOREM_CONVERSATIONAL_DEED.txt")
set(R16_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R16_TERMINAL_THEOREM_HANDOFF.rest")
set(R16_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R16_GENERATED_TRACE_THREE.lean")
set(R16_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R16_GENERATED_TRACE_THREE.olean")
set(R16_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R16_LEAN_STDOUT.txt")
set(R16_STDERR "${PROJECT_BINARY_DIR}/artifacts/R16_LEAN_STDERR.txt")
add_test(NAME r16.two_theorem_conversational_device_deed
  COMMAND r16_two_theorem_conversational_device_deed "${R16_DEED_ARTIFACT}"
    "${R15_HANDOFF_REST}" "${R15_DEED_B_SETUP}" "${R14_DEED_ARTIFACT}" "${R14_OLEAN}"
    "${R16_FINAL_REST}" "${R16_SOURCE}" "${R16_OLEAN}" "${R16_STDOUT}" "${R16_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts")
set_tests_properties(r16.two_theorem_conversational_device_deed PROPERTIES
  DEPENDS "r14.first_theorem_production_device_deed;r15.return_conditioned_morphology_device_deed")
add_test(NAME r16.terminal_theorem_host_conformance
  COMMAND r16_terminal_theorem_host_conformance)
add_test(NAME r16.forbidden_dependent_theorem_copy
  COMMAND "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_dependent_theorem_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R16_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r16_two_theorem_conversational_device_deed>|${R16_DEVICE_PTX}|${R16_DEVICE_CUBIN}")
set(R16_DEVICE_PTX_LIST "${R16_DEVICE_PTX}")
set(R16_DEVICE_CUBIN_LIST "${R16_DEVICE_CUBIN}")
