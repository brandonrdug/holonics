find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r20_regular_singular_store STATIC
  apparatus/host/regular_singular_store_adapter.cpp)
target_link_libraries(r20_regular_singular_store
  PRIVATE holonics::apparatus holonics_contract_options)

add_library(r20_regular_singular_executor STATIC
  apparatus/host/lean_checker_process.cpp
  cuda/executor/r20_regular_singular_executor.cu
  cuda/executor/r20_regular_singular_kernels.cu)
target_link_libraries(r20_regular_singular_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r20_regular_singular_device_deed
  apparatus/host/r20_regular_singular_deed.cpp
  tests/model/r20_artifact.cpp
  tests/model/r20_cases.cpp
  tests/model/r20_verify.cpp)
target_include_directories(r20_regular_singular_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r20_regular_singular_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r20_regular_singular_store
    r20_regular_singular_executor CUDA::cudart)

add_executable(r20_regular_singular_host_conformance
  tests/conformance/r20_regular_singular_host_conformance.cpp
  tests/model/r20_cases.cpp)
target_include_directories(r20_regular_singular_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r20_regular_singular_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r20_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r20_regular_singular_device_deed>
  DEPENDS r20_regular_singular_device_deed VERBATIM)

file(GLOB_RECURSE R20_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R20_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r20_regular_singular_kernels.cu")
set(R20_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r20_regular_singular_kernels.ptx")
set(R20_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r20_regular_singular_kernels.cubin")
set(R20_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R20_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R20_DEVICE_COMMON_FLAGS} --ptx
    "${R20_DEVICE_SOURCE}" -o "${R20_DEVICE_PTX}"
  DEPENDS "${R20_DEVICE_SOURCE}" ${R20_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R20_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R20_DEVICE_COMMON_FLAGS} --cubin
    "${R20_DEVICE_SOURCE}" -o "${R20_DEVICE_CUBIN}"
  DEPENDS "${R20_DEVICE_SOURCE}" ${R20_DEVICE_HEADERS} VERBATIM)
add_custom_target(r20_device_artifacts ALL DEPENDS ${R20_DEVICE_PTX} ${R20_DEVICE_CUBIN})

string(JOIN " " R20_DEVICE_FLAGS_RECEIPT ${R20_DEVICE_COMMON_FLAGS})
set(R20_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R20_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r20_regular_singular_kernels.cu -o <BUILD>/generated/r20_regular_singular_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R20_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r20_regular_singular_kernels.cu -o <BUILD>/generated/r20_regular_singular_kernels.cubin\n"
  "exterior_checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R20_GENERATED_REGULAR_SINGULAR.olean <BUILD>/artifacts/R20_GENERATED_REGULAR_SINGULAR.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts")
set(R20_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R20_REGULAR_SINGULAR_DEED.txt")
set(R20_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R20_REGULAR_SINGULAR_HANDOFF.rest")
set(R20_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R20_GENERATED_REGULAR_SINGULAR.lean")
set(R20_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R20_GENERATED_REGULAR_SINGULAR.olean")
set(R20_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R20_LEAN_STDOUT.txt")
set(R20_STDERR "${PROJECT_BINARY_DIR}/artifacts/R20_LEAN_STDERR.txt")
set(R20_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R20_REGULAR_SINGULAR_ATLAS.tsv")
holonic_found(NAME r20.regular_singular_device_deed
  EXECUTABLE r20_regular_singular_device_deed
  COMMAND
    "${R20_DEED_ARTIFACT}" "${R19_FINAL_REST}" "${R20_FINAL_REST}" "${R20_SOURCE}"
    "${R20_OLEAN}" "${R20_STDOUT}" "${R20_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R20_ATLAS}")
holonic_found(NAME r20.regular_singular_host_conformance
  EXECUTABLE r20_regular_singular_host_conformance
  COMMAND
   )
add_test(NAME r20.forbidden_regular_singular_copy
  COMMAND "${CMAKE_COMMAND}" -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_regular_singular_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R20_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r20_regular_singular_device_deed>|${R20_DEVICE_PTX}|${R20_DEVICE_CUBIN}")
set(R20_DEVICE_PTX_LIST "${R20_DEVICE_PTX}")
set(R20_DEVICE_CUBIN_LIST "${R20_DEVICE_CUBIN}")
