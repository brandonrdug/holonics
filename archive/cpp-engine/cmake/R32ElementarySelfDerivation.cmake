find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r32_elementary_store STATIC
  src/apparatus/host/elementary_card_adapter.cpp src/apparatus/host/elementary_rest_adapter.cpp)
target_link_libraries(r32_elementary_store PRIVATE holonics::apparatus holonics_contract_options)

add_library(r32_elementary_executor STATIC src/apparatus/host/lean_checker_process.cpp
  src/apparatus/host/returned_theorem_checker_process.cpp
  src/cuda/executor/r32_elementary_currents.cu src/cuda/executor/r32_elementary_kernels.cu
  src/cuda/executor/r32_discovery_executor.cu src/cuda/executor/r32_application_executor.cu)
target_link_libraries(r32_elementary_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r32_elementary_discovery_device_deed src/apparatus/host/r32_elementary_discovery_deed.cpp)
target_link_libraries(r32_elementary_discovery_device_deed PRIVATE holonics::apparatus
  holonics_contract_options r31_cultivated_store r32_elementary_store r32_elementary_executor CUDA::cudart)
add_executable(r32_heldout_holonomy_device_deed src/apparatus/host/r32_heldout_holonomy_deed.cpp)
target_link_libraries(r32_heldout_holonomy_device_deed PRIVATE holonics::apparatus
  holonics_contract_options r32_elementary_store r32_elementary_executor CUDA::cudart)
add_executable(r32_elementary_host_conformance
  tests/conformance/r32_elementary_host_conformance.cpp)
target_link_libraries(r32_elementary_host_conformance PRIVATE holonics_contract_options)

file(GLOB_RECURSE R32_DEVICE_HEADERS CONFIGURE_DEPENDS "${PROJECT_SOURCE_DIR}/src/include/holonics/*.hpp")
set(R32_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/r32_elementary_kernels.cu")
set(R32_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r32_elementary_kernels.ptx")
set(R32_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r32_elementary_kernels.cubin")
set(R32_DEVICE_COMMON_FLAGS --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false
  --Werror=all-warnings -I${PROJECT_SOURCE_DIR}/src/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R32_DEVICE_PTX}" COMMAND "${CMAKE_CUDA_COMPILER}"
  ${R32_DEVICE_COMMON_FLAGS} --ptx "${R32_DEVICE_SOURCE}" -o "${R32_DEVICE_PTX}"
  DEPENDS "${R32_DEVICE_SOURCE}" ${R32_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R32_DEVICE_CUBIN}" COMMAND "${CMAKE_CUDA_COMPILER}"
  ${R32_DEVICE_COMMON_FLAGS} --cubin "${R32_DEVICE_SOURCE}" -o "${R32_DEVICE_CUBIN}"
  DEPENDS "${R32_DEVICE_SOURCE}" ${R32_DEVICE_HEADERS} VERBATIM)
add_custom_target(r32_device_artifacts ALL DEPENDS ${R32_DEVICE_PTX} ${R32_DEVICE_CUBIN})

string(JOIN " " R32_DEVICE_FLAGS_RECEIPT ${R32_DEVICE_COMMON_FLAGS})
set(R32_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R32_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r32_elementary_kernels.cu -o <BUILD>/generated/r32_elementary_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R32_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r32_elementary_kernels.cu -o <BUILD>/generated/r32_elementary_kernels.cubin\n"
  "checker_discovery=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R32_ELEMENTARY_CAUSAL_CALCULUS.olean <BUILD>/artifacts/R32_ELEMENTARY_CAUSAL_CALCULUS.lean\n"
  "checker_application=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R32_HELDOUT_HOLONOMY.olean <BUILD>/artifacts/R32_HELDOUT_HOLONOMY.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts" "${PROJECT_BINARY_DIR}/receipts")
set(R32_DISC_DEED "${PROJECT_BINARY_DIR}/receipts/R32_ELEMENTARY_DISCOVERY_DEED.txt")
set(R32_INTERMEDIATE_REST "${PROJECT_BINARY_DIR}/artifacts/R32_ELEMENTARY_CALCULUS.rest")
set(R32_DISC_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R32_ELEMENTARY_CAUSAL_CALCULUS.lean")
set(R32_DISC_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R32_ELEMENTARY_CAUSAL_CALCULUS.olean")
set(R32_DISC_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R32_DISCOVERY_STDOUT.txt")
set(R32_DISC_STDERR "${PROJECT_BINARY_DIR}/artifacts/R32_DISCOVERY_STDERR.txt")
set(R32_A0 "${PROJECT_BINARY_DIR}/artifacts/R32_IDENTITY_INCIDENCE_ATLAS.tsv")
set(R32_A1 "${PROJECT_BINARY_DIR}/artifacts/R32_COMPOSITION_ATLAS.tsv")
set(R32_A2 "${PROJECT_BINARY_DIR}/artifacts/R32_RECEIVER_ATLAS.tsv")
set(R32_A3 "${PROJECT_BINARY_DIR}/artifacts/R32_CHART_ATLAS.tsv")
set(R32_A4 "${PROJECT_BINARY_DIR}/artifacts/R32_CONDUCT_ATLAS.tsv")
set(R32_A5 "${PROJECT_BINARY_DIR}/artifacts/R32_CONNECTED_LAW_ATLAS.tsv")
set(R32_APP_DEED "${PROJECT_BINARY_DIR}/receipts/R32_HELDOUT_HOLONOMY_DEED.txt")
set(R32_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R32_SELF_DERIVATION_HANDOFF.rest")
set(R32_APP_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R32_HELDOUT_HOLONOMY.lean")
set(R32_APP_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R32_HELDOUT_HOLONOMY.olean")
set(R32_APP_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R32_APPLICATION_STDOUT.txt")
set(R32_APP_STDERR "${PROJECT_BINARY_DIR}/artifacts/R32_APPLICATION_STDERR.txt")
set(R32_DOSSIER "${PROJECT_BINARY_DIR}/artifacts/R32_ELEMENTARY_CAUSAL_CALCULUS_DOSSIER.md")
set(R32_APP_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R32_HELDOUT_HOLONOMY_ATLAS.tsv")
set(R32_SOURCE_AUDIT "${PROJECT_BINARY_DIR}/receipts/R32_SOURCE_ACCESS_AUDIT.txt")
set(R32_HOST_CONFORMANCE "${PROJECT_BINARY_DIR}/receipts/R32_HOST_CONFORMANCE.txt")
set(R32_DETERMINISM "${PROJECT_BINARY_DIR}/receipts/R32_DETERMINISM.txt")
set(R32_SEAL "${PROJECT_BINARY_DIR}/receipts/R32_SEALED_RETURN.txt")
set(R32_CANON_COMPARISON "${PROJECT_BINARY_DIR}/artifacts/R32_POST_SEAL_CANON_COMPARISON.md")
include(cmake/R32ElementaryTests.cmake)

set(R32_EXTRA_ARTIFACTS "$<TARGET_FILE:r32_elementary_discovery_device_deed>|$<TARGET_FILE:r32_heldout_holonomy_device_deed>|$<TARGET_FILE:r32_elementary_host_conformance>|${R32_DEVICE_PTX}|${R32_DEVICE_CUBIN}")
set(R32_DEVICE_PTX_LIST "${R32_DEVICE_PTX}")
set(R32_DEVICE_CUBIN_LIST "${R32_DEVICE_CUBIN}")
