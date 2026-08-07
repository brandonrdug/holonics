find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r22_cm_incidence_store STATIC
  src/apparatus/host/cm_incidence_card_adapter.cpp
  src/apparatus/host/cm_incidence_store_adapter.cpp)
target_link_libraries(r22_cm_incidence_store
  PRIVATE holonics::apparatus holonics_contract_options)

add_library(r22_cm_incidence_executor STATIC
  src/apparatus/host/lean_checker_process.cpp
  src/cuda/executor/r22_cm_incidence_executor.cu
  src/cuda/executor/r22_cm_incidence_kernels.cu
  src/cuda/executor/r22_cm_incidence_probe.cu)
target_link_libraries(r22_cm_incidence_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r22_cm_incidence_device_deed
  src/apparatus/host/r22_cm_incidence_deed.cpp
  tests/model/r22_artifact.cpp
  tests/model/r22_atlas.cpp
  tests/model/r22_cases.cpp
  tests/model/r22_verify.cpp)
target_include_directories(r22_cm_incidence_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r22_cm_incidence_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r22_cm_incidence_store
    r22_cm_incidence_executor CUDA::cudart)

add_executable(r22_cm_incidence_host_conformance
  tests/conformance/r22_cm_incidence_host_conformance.cpp
  tests/model/r22_cases.cpp)
target_include_directories(r22_cm_incidence_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r22_cm_incidence_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r22_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r22_cm_incidence_device_deed>
  DEPENDS r22_cm_incidence_device_deed VERBATIM)

file(GLOB_RECURSE R22_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/*.hpp")
set(R22_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/r22_cm_incidence_kernels.cu")
set(R22_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r22_cm_incidence_kernels.ptx")
set(R22_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r22_cm_incidence_kernels.cubin")
set(R22_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/src/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R22_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R22_DEVICE_COMMON_FLAGS} --ptx
    "${R22_DEVICE_SOURCE}" -o "${R22_DEVICE_PTX}"
  DEPENDS "${R22_DEVICE_SOURCE}" ${R22_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R22_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R22_DEVICE_COMMON_FLAGS} --cubin
    "${R22_DEVICE_SOURCE}" -o "${R22_DEVICE_CUBIN}"
  DEPENDS "${R22_DEVICE_SOURCE}" ${R22_DEVICE_HEADERS} VERBATIM)
add_custom_target(r22_device_artifacts ALL DEPENDS ${R22_DEVICE_PTX} ${R22_DEVICE_CUBIN})

string(JOIN " " R22_DEVICE_FLAGS_RECEIPT ${R22_DEVICE_COMMON_FLAGS})
set(R22_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R22_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r22_cm_incidence_kernels.cu -o <BUILD>/generated/r22_cm_incidence_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R22_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r22_cm_incidence_kernels.cu -o <BUILD>/generated/r22_cm_incidence_kernels.cubin\n"
  "checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R22_GENERATED_CM_INCIDENCE.olean <BUILD>/artifacts/R22_GENERATED_CM_INCIDENCE.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts" "${PROJECT_BINARY_DIR}/receipts")
set(R22_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R22_CM_INCIDENCE_DEED.txt")
set(R22_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R22_CM_INCIDENCE_HANDOFF.rest")
set(R22_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R22_GENERATED_CM_INCIDENCE.lean")
set(R22_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R22_GENERATED_CM_INCIDENCE.olean")
set(R22_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R22_LEAN_STDOUT.txt")
set(R22_STDERR "${PROJECT_BINARY_DIR}/artifacts/R22_LEAN_STDERR.txt")
set(R22_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R22_CM_INCIDENCE_ATLAS.tsv")
holonic_found(NAME r22.cm_incidence_device_deed
  EXECUTABLE r22_cm_incidence_device_deed
  COMMAND
    "${R22_DEED_ARTIFACT}" "${R21_FINAL_REST}" "${R22_FINAL_REST}"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R22_CM_INCIDENCE.card" "${R22_SOURCE}"
    "${R22_OLEAN}" "${R22_STDOUT}" "${R22_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R22_ATLAS}")
holonic_found(NAME r22.cm_incidence_host_conformance
  EXECUTABLE r22_cm_incidence_host_conformance
  COMMAND
   )
add_test(NAME r22.forbidden_cm_incidence_copy
  COMMAND "${CMAKE_COMMAND}" -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_cm_incidence_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/src/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R22_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r22_cm_incidence_device_deed>|${R22_DEVICE_PTX}|${R22_DEVICE_CUBIN}")
set(R22_DEVICE_PTX_LIST "${R22_DEVICE_PTX}")
set(R22_DEVICE_CUBIN_LIST "${R22_DEVICE_CUBIN}")
