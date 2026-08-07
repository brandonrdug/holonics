find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r26_intrinsic_hypergeometry_store STATIC
  src/apparatus/host/intrinsic_hypergeometry_card_adapter.cpp
  src/apparatus/host/intrinsic_hypergeometry_store_adapter.cpp)
target_link_libraries(r26_intrinsic_hypergeometry_store
  PRIVATE holonics::apparatus holonics_contract_options)

add_library(r26_intrinsic_hypergeometry_executor STATIC
  src/apparatus/host/lean_checker_process.cpp
  src/cuda/executor/r26_intrinsic_hypergeometry_executor.cu
  src/cuda/executor/r26_intrinsic_hypergeometry_kernels.cu)
target_link_libraries(r26_intrinsic_hypergeometry_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r26_intrinsic_hypergeometry_device_deed
  src/apparatus/host/r26_intrinsic_hypergeometry_deed.cpp
  tests/model/r26_artifact.cpp
  tests/model/r26_atlas.cpp
  tests/model/r26_cases.cpp
  tests/model/r26_verify.cpp)
target_include_directories(r26_intrinsic_hypergeometry_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r26_intrinsic_hypergeometry_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r22_cm_incidence_store
    r24_algebraic_variation_store r26_intrinsic_hypergeometry_store
    r26_intrinsic_hypergeometry_executor CUDA::cudart)

add_executable(r26_intrinsic_hypergeometry_host_conformance
  tests/conformance/r26_intrinsic_hypergeometry_host_conformance.cpp
  tests/model/r22_cases.cpp
  tests/model/r23_cases.cpp
  tests/model/r24_cases.cpp
  tests/model/r26_cases.cpp)
target_include_directories(r26_intrinsic_hypergeometry_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r26_intrinsic_hypergeometry_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r26_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r26_intrinsic_hypergeometry_device_deed>
  DEPENDS r26_intrinsic_hypergeometry_device_deed VERBATIM)

file(GLOB_RECURSE R26_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/*.hpp")
set(R26_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/r26_intrinsic_hypergeometry_kernels.cu")
set(R26_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r26_intrinsic_hypergeometry_kernels.ptx")
set(R26_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r26_intrinsic_hypergeometry_kernels.cubin")
set(R26_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/src/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R26_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R26_DEVICE_COMMON_FLAGS} --ptx
    "${R26_DEVICE_SOURCE}" -o "${R26_DEVICE_PTX}"
  DEPENDS "${R26_DEVICE_SOURCE}" ${R26_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R26_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R26_DEVICE_COMMON_FLAGS} --cubin
    "${R26_DEVICE_SOURCE}" -o "${R26_DEVICE_CUBIN}"
  DEPENDS "${R26_DEVICE_SOURCE}" ${R26_DEVICE_HEADERS} VERBATIM)
add_custom_target(r26_device_artifacts ALL DEPENDS ${R26_DEVICE_PTX} ${R26_DEVICE_CUBIN})

string(JOIN " " R26_DEVICE_FLAGS_RECEIPT ${R26_DEVICE_COMMON_FLAGS})
set(R26_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R26_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r26_intrinsic_hypergeometry_kernels.cu -o <BUILD>/generated/r26_intrinsic_hypergeometry_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R26_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r26_intrinsic_hypergeometry_kernels.cu -o <BUILD>/generated/r26_intrinsic_hypergeometry_kernels.cubin\n"
  "checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R26_GENERATED_INTRINSIC_HYPERGEOMETRY.olean <BUILD>/artifacts/R26_GENERATED_INTRINSIC_HYPERGEOMETRY.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts" "${PROJECT_BINARY_DIR}/receipts")
set(R26_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R26_INTRINSIC_HYPERGEOMETRY_DEED.txt")
set(R26_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R26_INTRINSIC_HYPERGEOMETRY_HANDOFF.rest")
set(R26_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R26_GENERATED_INTRINSIC_HYPERGEOMETRY.lean")
set(R26_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R26_GENERATED_INTRINSIC_HYPERGEOMETRY.olean")
set(R26_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R26_LEAN_STDOUT.txt")
set(R26_STDERR "${PROJECT_BINARY_DIR}/artifacts/R26_LEAN_STDERR.txt")
set(R26_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R26_INTRINSIC_HYPERGEOMETRY_ATLAS.tsv")
holonic_found(NAME r26.intrinsic_hypergeometry_device_deed
  EXECUTABLE r26_intrinsic_hypergeometry_device_deed
  COMMAND
    "${R26_DEED_ARTIFACT}" "${R25_FINAL_REST}" "${R26_FINAL_REST}"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R26_INTRINSIC_HYPERGEOMETRY.card"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R22_CM_INCIDENCE.card"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R24_ALGEBRAIC_VARIATION.card" "${R26_SOURCE}"
    "${R26_OLEAN}" "${R26_STDOUT}" "${R26_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R26_ATLAS}")
holonic_found(NAME r26.intrinsic_hypergeometry_host_conformance
  EXECUTABLE r26_intrinsic_hypergeometry_host_conformance
  COMMAND
   )
add_test(NAME r26.forbidden_intrinsic_hypergeometry_copy
  COMMAND "${CMAKE_COMMAND}" -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_intrinsic_hypergeometry_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/src/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R26_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r26_intrinsic_hypergeometry_device_deed>|${R26_DEVICE_PTX}|${R26_DEVICE_CUBIN}")
set(R26_DEVICE_PTX_LIST "${R26_DEVICE_PTX}")
set(R26_DEVICE_CUBIN_LIST "${R26_DEVICE_CUBIN}")
