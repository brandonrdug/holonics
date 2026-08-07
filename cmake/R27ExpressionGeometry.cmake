find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r27_expression_geometry_store STATIC
  apparatus/host/expression_geometry_card_adapter.cpp
  apparatus/host/expression_geometry_store_adapter.cpp)
target_link_libraries(r27_expression_geometry_store
  PRIVATE holonics::apparatus holonics_contract_options)

add_library(r27_expression_geometry_executor STATIC
  apparatus/host/lean_checker_process.cpp
  cuda/executor/r27_expression_geometry_executor.cu
  cuda/executor/r27_expression_geometry_kernels.cu)
target_link_libraries(r27_expression_geometry_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r27_expression_geometry_device_deed
  apparatus/host/r27_expression_geometry_deed.cpp
  tests/model/r27_artifact.cpp
  tests/model/r27_atlas.cpp
  tests/model/r27_cases.cpp
  tests/model/r27_verify.cpp)
target_include_directories(r27_expression_geometry_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r27_expression_geometry_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r27_expression_geometry_store
    r27_expression_geometry_executor CUDA::cudart)

add_executable(r27_expression_geometry_host_conformance
  tests/conformance/r27_expression_geometry_host_conformance.cpp
  tests/model/r27_cases.cpp)
target_include_directories(r27_expression_geometry_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r27_expression_geometry_host_conformance
  PRIVATE holonics::event holonics_contract_options CUDA::cudart)

add_custom_target(r27_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r27_expression_geometry_device_deed>
  DEPENDS r27_expression_geometry_device_deed VERBATIM)

file(GLOB_RECURSE R27_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R27_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r27_expression_geometry_kernels.cu")
set(R27_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r27_expression_geometry_kernels.ptx")
set(R27_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r27_expression_geometry_kernels.cubin")
set(R27_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R27_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R27_DEVICE_COMMON_FLAGS} --ptx
    "${R27_DEVICE_SOURCE}" -o "${R27_DEVICE_PTX}"
  DEPENDS "${R27_DEVICE_SOURCE}" ${R27_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R27_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R27_DEVICE_COMMON_FLAGS} --cubin
    "${R27_DEVICE_SOURCE}" -o "${R27_DEVICE_CUBIN}"
  DEPENDS "${R27_DEVICE_SOURCE}" ${R27_DEVICE_HEADERS} VERBATIM)
add_custom_target(r27_device_artifacts ALL DEPENDS ${R27_DEVICE_PTX} ${R27_DEVICE_CUBIN})

string(JOIN " " R27_DEVICE_FLAGS_RECEIPT ${R27_DEVICE_COMMON_FLAGS})
set(R27_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R27_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r27_expression_geometry_kernels.cu -o <BUILD>/generated/r27_expression_geometry_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R27_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r27_expression_geometry_kernels.cu -o <BUILD>/generated/r27_expression_geometry_kernels.cubin\n"
  "checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R27_GENERATED_EXPRESSION_GEOMETRY.olean <BUILD>/artifacts/R27_GENERATED_EXPRESSION_GEOMETRY.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts" "${PROJECT_BINARY_DIR}/receipts")
set(R27_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R27_EXPRESSION_GEOMETRY_DEED.txt")
set(R27_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R27_EXPRESSION_GEOMETRY_HANDOFF.rest")
set(R27_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R27_GENERATED_EXPRESSION_GEOMETRY.lean")
set(R27_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R27_GENERATED_EXPRESSION_GEOMETRY.olean")
set(R27_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R27_LEAN_STDOUT.txt")
set(R27_STDERR "${PROJECT_BINARY_DIR}/artifacts/R27_LEAN_STDERR.txt")
set(R27_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R27_EXPRESSION_GEOMETRY_ATLAS.tsv")
holonic_found(NAME r27.expression_geometry_device_deed
  EXECUTABLE r27_expression_geometry_device_deed
  COMMAND
    "${R27_DEED_ARTIFACT}" "${R26_FINAL_REST}" "${R27_FINAL_REST}"
    "${PROJECT_SOURCE_DIR}/apparatus/cards/R27_EXPRESSION_GEOMETRY.card" "${R27_SOURCE}"
    "${R27_OLEAN}" "${R27_STDOUT}" "${R27_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R27_ATLAS}")
holonic_found(NAME r27.expression_geometry_host_conformance
  EXECUTABLE r27_expression_geometry_host_conformance
  COMMAND
   )
add_test(NAME r27.forbidden_expression_geometry_copy
  COMMAND "${CMAKE_COMMAND}" -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_expression_geometry_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R27_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r27_expression_geometry_device_deed>|${R27_DEVICE_PTX}|${R27_DEVICE_CUBIN}")
set(R27_DEVICE_PTX_LIST "${R27_DEVICE_PTX}")
set(R27_DEVICE_CUBIN_LIST "${R27_DEVICE_CUBIN}")
