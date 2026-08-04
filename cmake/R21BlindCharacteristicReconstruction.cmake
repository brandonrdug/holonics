find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r21_blind_reconstruction_store STATIC
  apparatus/host/blind_reconstruction_card_adapter.cpp
  apparatus/host/blind_reconstruction_store_adapter.cpp)
target_link_libraries(r21_blind_reconstruction_store
  PRIVATE holonics::apparatus holonics_contract_options)

add_library(r21_blind_reconstruction_executor STATIC
  apparatus/host/lean_checker_process.cpp
  cuda/executor/r21_blind_reconstruction_executor.cu
  cuda/executor/r21_blind_reconstruction_kernels.cu
  cuda/executor/r21_blind_reconstruction_probe.cu)
target_link_libraries(r21_blind_reconstruction_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r21_blind_reconstruction_device_deed
  apparatus/host/r21_blind_reconstruction_deed.cpp
  tests/model/r21_artifact.cpp
  tests/model/r21_atlas.cpp
  tests/model/r21_cases.cpp
  tests/model/r21_verify.cpp)
target_include_directories(r21_blind_reconstruction_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r21_blind_reconstruction_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r21_blind_reconstruction_store
    r21_blind_reconstruction_executor CUDA::cudart)

add_executable(r21_blind_reconstruction_host_conformance
  tests/conformance/r21_blind_reconstruction_host_conformance.cpp
  tests/model/r21_cases.cpp)
target_include_directories(r21_blind_reconstruction_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r21_blind_reconstruction_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r21_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r21_blind_reconstruction_device_deed>
  DEPENDS r21_blind_reconstruction_device_deed VERBATIM)

file(GLOB_RECURSE R21_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R21_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r21_blind_reconstruction_kernels.cu")
set(R21_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r21_blind_reconstruction_kernels.ptx")
set(R21_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r21_blind_reconstruction_kernels.cubin")
set(R21_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R21_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R21_DEVICE_COMMON_FLAGS} --ptx
    "${R21_DEVICE_SOURCE}" -o "${R21_DEVICE_PTX}"
  DEPENDS "${R21_DEVICE_SOURCE}" ${R21_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R21_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R21_DEVICE_COMMON_FLAGS} --cubin
    "${R21_DEVICE_SOURCE}" -o "${R21_DEVICE_CUBIN}"
  DEPENDS "${R21_DEVICE_SOURCE}" ${R21_DEVICE_HEADERS} VERBATIM)
add_custom_target(r21_device_artifacts ALL DEPENDS ${R21_DEVICE_PTX} ${R21_DEVICE_CUBIN})

string(JOIN " " R21_DEVICE_FLAGS_RECEIPT ${R21_DEVICE_COMMON_FLAGS})
set(R21_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R21_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r21_blind_reconstruction_kernels.cu -o <BUILD>/generated/r21_blind_reconstruction_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R21_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r21_blind_reconstruction_kernels.cu -o <BUILD>/generated/r21_blind_reconstruction_kernels.cubin\n"
  "code_checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R21_GENERATED_CODE_RECONSTRUCTION.olean <BUILD>/artifacts/R21_GENERATED_CODE_RECONSTRUCTION.lean\n"
  "moment_checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R21_GENERATED_MOMENT_RECONSTRUCTION.olean <BUILD>/artifacts/R21_GENERATED_MOMENT_RECONSTRUCTION.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts")
set(R21_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R21_BLIND_RECONSTRUCTION_DEED.txt")
set(R21_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R21_BLIND_RECONSTRUCTION_HANDOFF.rest")
set(R21_CODE_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R21_GENERATED_CODE_RECONSTRUCTION.lean")
set(R21_CODE_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R21_GENERATED_CODE_RECONSTRUCTION.olean")
set(R21_CODE_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R21_CODE_LEAN_STDOUT.txt")
set(R21_CODE_STDERR "${PROJECT_BINARY_DIR}/artifacts/R21_CODE_LEAN_STDERR.txt")
set(R21_MOMENT_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R21_GENERATED_MOMENT_RECONSTRUCTION.lean")
set(R21_MOMENT_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R21_GENERATED_MOMENT_RECONSTRUCTION.olean")
set(R21_MOMENT_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R21_MOMENT_LEAN_STDOUT.txt")
set(R21_MOMENT_STDERR "${PROJECT_BINARY_DIR}/artifacts/R21_MOMENT_LEAN_STDERR.txt")
set(R21_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R21_BLIND_CHARACTERISTIC_ATLAS.tsv")
add_test(NAME r21.blind_reconstruction_device_deed
  COMMAND r21_blind_reconstruction_device_deed "${R21_DEED_ARTIFACT}"
    "${R20_FINAL_REST}" "${R21_FINAL_REST}"
    "${PROJECT_SOURCE_DIR}/apparatus/cards/R21_BINARY_CODE_PROBLEM.card"
    "${PROJECT_SOURCE_DIR}/apparatus/cards/R21_GAPCVP_MOMENTS.card"
    "${R21_CODE_SOURCE}" "${R21_CODE_OLEAN}" "${R21_CODE_STDOUT}" "${R21_CODE_STDERR}"
    "${R21_MOMENT_SOURCE}" "${R21_MOMENT_OLEAN}" "${R21_MOMENT_STDOUT}"
    "${R21_MOMENT_STDERR}" "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R21_ATLAS}")
set_tests_properties(r21.blind_reconstruction_device_deed PROPERTIES
  DEPENDS "r20.regular_singular_device_deed")
add_test(NAME r21.blind_reconstruction_host_conformance
  COMMAND r21_blind_reconstruction_host_conformance)
add_test(NAME r21.forbidden_blind_reconstruction_copy
  COMMAND "${CMAKE_COMMAND}" -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_blind_reconstruction_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R21_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r21_blind_reconstruction_device_deed>|${R21_DEVICE_PTX}|${R21_DEVICE_CUBIN}")
set(R21_DEVICE_PTX_LIST "${R21_DEVICE_PTX}")
set(R21_DEVICE_CUBIN_LIST "${R21_DEVICE_CUBIN}")
