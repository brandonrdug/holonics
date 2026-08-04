find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r13_lean_checker_executor STATIC
  apparatus/host/lean_checker_process.cpp
  cuda/executor/r13_lean_checker_executor.cu
  cuda/executor/r13_lean_checker_kernels.cu)
target_link_libraries(r13_lean_checker_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r13_lean_checker_device_deed
  apparatus/host/r13_lean_exterior_checker_deed.cpp
  tests/model/r13_artifact.cpp
  tests/model/r13_cases.cpp
  tests/model/r13_verify.cpp)
target_include_directories(r13_lean_checker_device_deed PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r13_lean_checker_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r13_lean_checker_executor CUDA::cudart)

add_executable(r13_lean_checker_host_conformance
  tests/conformance/r13_lean_checker_host_conformance.cpp)
target_link_libraries(r13_lean_checker_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r13_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r13_lean_checker_device_deed>
  DEPENDS r13_lean_checker_device_deed VERBATIM)

file(GLOB_RECURSE R13_DEVICE_HEADERS CONFIGURE_DEPENDS "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R13_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r13_lean_checker_kernels.cu")
set(R13_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r13_lean_checker_kernels.ptx")
set(R13_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r13_lean_checker_kernels.cubin")
set(R13_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R13_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R13_DEVICE_COMMON_FLAGS} --ptx
    "${R13_DEVICE_SOURCE}" -o "${R13_DEVICE_PTX}"
  DEPENDS "${R13_DEVICE_SOURCE}" ${R13_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R13_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R13_DEVICE_COMMON_FLAGS} --cubin
    "${R13_DEVICE_SOURCE}" -o "${R13_DEVICE_CUBIN}"
  DEPENDS "${R13_DEVICE_SOURCE}" ${R13_DEVICE_HEADERS} VERBATIM)
add_custom_target(r13_device_artifacts ALL DEPENDS ${R13_DEVICE_PTX} ${R13_DEVICE_CUBIN})

string(JOIN " " R13_DEVICE_FLAGS_RECEIPT ${R13_DEVICE_COMMON_FLAGS})
set(R13_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R13_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r13_lean_checker_kernels.cu -o <BUILD>/generated/r13_lean_checker_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R13_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r13_lean_checker_kernels.cu -o <BUILD>/generated/r13_lean_checker_kernels.cubin\n"
  "exterior_checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R13_GENERATED_REBASE_REVERSE.olean <BUILD>/artifacts/R13_GENERATED_REBASE_REVERSE.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts")
set(R13_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R13_LEAN_EXTERIOR_CHECKER_DEED.txt")
set(R13_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R13_GENERATED_REBASE_REVERSE.lean")
set(R13_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R13_GENERATED_REBASE_REVERSE.olean")
set(R13_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R13_LEAN_STDOUT.txt")
set(R13_STDERR "${PROJECT_BINARY_DIR}/artifacts/R13_LEAN_STDERR.txt")
add_test(NAME r13.lean_checker_device_deed
  COMMAND r13_lean_checker_device_deed "${R13_DEED_ARTIFACT}"
    "${R12_GENERATED_SOURCE}" "${R13_SOURCE}" "${R13_OLEAN}" "${R13_STDOUT}" "${R13_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts")
set_tests_properties(r13.lean_checker_device_deed PROPERTIES
  DEPENDS "r12.generative_math_device_deed")
add_test(NAME r13.lean_checker_host_conformance COMMAND r13_lean_checker_host_conformance)
add_test(NAME r13.forbidden_checker_pending_copy
  COMMAND "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_checker_pending_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R13_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r13_lean_checker_device_deed>|${R13_DEVICE_PTX}|${R13_DEVICE_CUBIN}")
set(R13_DEVICE_PTX_LIST "${R13_DEVICE_PTX}")
set(R13_DEVICE_CUBIN_LIST "${R13_DEVICE_CUBIN}")
