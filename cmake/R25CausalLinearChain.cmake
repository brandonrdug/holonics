find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r25_causal_linear_store STATIC
  apparatus/host/causal_linear_card_adapter.cpp
  apparatus/host/causal_linear_store_adapter.cpp)
target_link_libraries(r25_causal_linear_store
  PRIVATE holonics::apparatus holonics_contract_options)

add_library(r25_causal_linear_executor STATIC
  apparatus/host/lean_checker_process.cpp
  cuda/executor/r25_causal_linear_executor.cu
  cuda/executor/r25_causal_linear_kernels.cu
  cuda/executor/r25_causal_linear_probe.cu)
target_link_libraries(r25_causal_linear_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r25_causal_linear_device_deed
  apparatus/host/r25_causal_linear_deed.cpp
  tests/model/r25_artifact.cpp
  tests/model/r25_cases.cpp
  tests/model/r25_verify.cpp)
target_include_directories(r25_causal_linear_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r25_causal_linear_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r22_cm_incidence_store
    r23_toric_cycle_store r24_algebraic_variation_store r25_causal_linear_store
    r25_causal_linear_executor CUDA::cudart)

add_executable(r25_causal_linear_host_conformance
  tests/conformance/r25_causal_linear_host_conformance.cpp
  tests/model/r22_cases.cpp
  tests/model/r23_cases.cpp
  tests/model/r24_cases.cpp
  tests/model/r25_cases.cpp)
target_include_directories(r25_causal_linear_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r25_causal_linear_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r25_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r25_causal_linear_device_deed>
  DEPENDS r25_causal_linear_device_deed VERBATIM)

file(GLOB_RECURSE R25_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R25_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r25_causal_linear_kernels.cu")
set(R25_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r25_causal_linear_kernels.ptx")
set(R25_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r25_causal_linear_kernels.cubin")
set(R25_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R25_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R25_DEVICE_COMMON_FLAGS} --ptx
    "${R25_DEVICE_SOURCE}" -o "${R25_DEVICE_PTX}"
  DEPENDS "${R25_DEVICE_SOURCE}" ${R25_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R25_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R25_DEVICE_COMMON_FLAGS} --cubin
    "${R25_DEVICE_SOURCE}" -o "${R25_DEVICE_CUBIN}"
  DEPENDS "${R25_DEVICE_SOURCE}" ${R25_DEVICE_HEADERS} VERBATIM)
add_custom_target(r25_device_artifacts ALL DEPENDS ${R25_DEVICE_PTX} ${R25_DEVICE_CUBIN})

string(JOIN " " R25_DEVICE_FLAGS_RECEIPT ${R25_DEVICE_COMMON_FLAGS})
set(R25_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R25_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r25_causal_linear_kernels.cu -o <BUILD>/generated/r25_causal_linear_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R25_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r25_causal_linear_kernels.cu -o <BUILD>/generated/r25_causal_linear_kernels.cubin\n"
  "checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R25_GENERATED_CAUSAL_LINEAR.olean <BUILD>/artifacts/R25_GENERATED_CAUSAL_LINEAR.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts" "${PROJECT_BINARY_DIR}/receipts")
set(R25_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R25_CAUSAL_LINEAR_DEED.txt")
set(R25_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R25_CAUSAL_LINEAR_HANDOFF.rest")
set(R25_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R25_GENERATED_CAUSAL_LINEAR.lean")
set(R25_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R25_GENERATED_CAUSAL_LINEAR.olean")
set(R25_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R25_LEAN_STDOUT.txt")
set(R25_STDERR "${PROJECT_BINARY_DIR}/artifacts/R25_LEAN_STDERR.txt")
set(R25_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R25_CAUSAL_LINEAR_ATLAS.tsv")
add_test(NAME r25.causal_linear_device_deed
  COMMAND r25_causal_linear_device_deed "${R25_DEED_ARTIFACT}"
    "${R24_FINAL_REST}" "${R25_FINAL_REST}"
    "${PROJECT_SOURCE_DIR}/apparatus/cards/R25_CAUSAL_LINEAR_CHAIN.card"
    "${PROJECT_SOURCE_DIR}/apparatus/cards/R22_CM_INCIDENCE.card"
    "${PROJECT_SOURCE_DIR}/apparatus/cards/R23_TORIC_CYCLE.card"
    "${PROJECT_SOURCE_DIR}/apparatus/cards/R24_ALGEBRAIC_VARIATION.card"
    "${R25_SOURCE}" "${R25_OLEAN}" "${R25_STDOUT}" "${R25_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R25_ATLAS}")
set_tests_properties(r25.causal_linear_device_deed PROPERTIES
  DEPENDS "r24.algebraic_variation_device_deed" TIMEOUT 120)
add_test(NAME r25.causal_linear_host_conformance
  COMMAND r25_causal_linear_host_conformance)
add_test(NAME r25.forbidden_causal_linear_copy
  COMMAND "${CMAKE_COMMAND}" -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_causal_linear_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R25_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r25_causal_linear_device_deed>|${R25_DEVICE_PTX}|${R25_DEVICE_CUBIN}")
set(R25_DEVICE_PTX_LIST "${R25_DEVICE_PTX}")
set(R25_DEVICE_CUBIN_LIST "${R25_DEVICE_CUBIN}")
