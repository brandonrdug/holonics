find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r35_trace_rebase_store STATIC
  src/apparatus/host/trace_rebase_card_adapter.cpp
  src/apparatus/host/trace_rebase_rest_adapter.cpp)
target_link_libraries(r35_trace_rebase_store PRIVATE holonics::apparatus
  holonics_contract_options)
add_library(r35_trace_rebase_executor STATIC
  src/apparatus/host/lean_checker_process.cpp
  src/apparatus/host/returned_theorem_checker_process.cpp
  src/cuda/executor/r35_trace_rebase_currents.cu
  src/cuda/executor/r35_trace_rebase_kernels.cu
  src/cuda/executor/r35_heldout_trace_rebase_kernels.cu
  src/cuda/executor/r35_trace_rebase_discovery_executor.cu
  src/cuda/executor/r35_trace_rebase_application_executor.cu)
target_link_libraries(r35_trace_rebase_executor PRIVATE holonics::apparatus
  holonics_contract_options CUDA::cudart)
add_executable(r35_trace_rebase_discovery_device_deed
  src/apparatus/host/r35_trace_rebase_discovery_deed.cpp)
target_link_libraries(r35_trace_rebase_discovery_device_deed PRIVATE
  holonics::apparatus holonics_contract_options r34_trace_fiber_store
  r35_trace_rebase_store r35_trace_rebase_executor CUDA::cudart)
add_executable(r35_trace_rebase_application_device_deed
  src/apparatus/host/r35_trace_rebase_application_deed.cpp)
target_link_libraries(r35_trace_rebase_application_device_deed PRIVATE
  holonics::apparatus holonics_contract_options r35_trace_rebase_store
  r35_trace_rebase_executor CUDA::cudart)
add_executable(r35_trace_rebase_host_conformance
  tests/conformance/r35_trace_rebase_host_conformance.cpp)
target_link_libraries(r35_trace_rebase_host_conformance PRIVATE
  holonics_contract_options)

file(GLOB_RECURSE R35_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/*.hpp")
set(R35_DEVICE_SOURCE
  "${PROJECT_SOURCE_DIR}/src/cuda/executor/r35_trace_rebase_kernels.cu")
set(R35_HELDOUT_DEVICE_SOURCE
  "${PROJECT_SOURCE_DIR}/src/cuda/executor/r35_heldout_trace_rebase_kernels.cu")
set(R35_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r35_trace_rebase_kernels.ptx")
set(R35_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r35_trace_rebase_kernels.cubin")
set(R35_HELDOUT_DEVICE_PTX
  "${R0_GENERATED_DIRECTORY}/r35_heldout_trace_rebase_kernels.ptx")
set(R35_HELDOUT_DEVICE_CUBIN
  "${R0_GENERATED_DIRECTORY}/r35_heldout_trace_rebase_kernels.cubin")
set(R35_DEVICE_COMMON_FLAGS --std=c++20 -O3 --gpu-architecture=sm_89
  --fmad=false --Werror=all-warnings -I${PROJECT_SOURCE_DIR}/src/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R35_DEVICE_PTX}" COMMAND "${CMAKE_CUDA_COMPILER}"
  ${R35_DEVICE_COMMON_FLAGS} --ptx "${R35_DEVICE_SOURCE}" -o "${R35_DEVICE_PTX}"
  DEPENDS "${R35_DEVICE_SOURCE}" ${R35_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R35_DEVICE_CUBIN}" COMMAND "${CMAKE_CUDA_COMPILER}"
  ${R35_DEVICE_COMMON_FLAGS} --cubin "${R35_DEVICE_SOURCE}" -o "${R35_DEVICE_CUBIN}"
  DEPENDS "${R35_DEVICE_SOURCE}" ${R35_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R35_HELDOUT_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R35_DEVICE_COMMON_FLAGS} --ptx
  "${R35_HELDOUT_DEVICE_SOURCE}" -o "${R35_HELDOUT_DEVICE_PTX}"
  DEPENDS "${R35_HELDOUT_DEVICE_SOURCE}" ${R35_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R35_HELDOUT_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R35_DEVICE_COMMON_FLAGS} --cubin
  "${R35_HELDOUT_DEVICE_SOURCE}" -o "${R35_HELDOUT_DEVICE_CUBIN}"
  DEPENDS "${R35_HELDOUT_DEVICE_SOURCE}" ${R35_DEVICE_HEADERS} VERBATIM)
add_custom_target(r35_device_artifacts ALL DEPENDS ${R35_DEVICE_PTX}
  ${R35_DEVICE_CUBIN} ${R35_HELDOUT_DEVICE_PTX} ${R35_HELDOUT_DEVICE_CUBIN})

string(JOIN " " R35_DEVICE_FLAGS_RECEIPT ${R35_DEVICE_COMMON_FLAGS})
set(R35_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R35_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r35_trace_rebase_kernels.cu -o <BUILD>/generated/r35_trace_rebase_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R35_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r35_trace_rebase_kernels.cu -o <BUILD>/generated/r35_trace_rebase_kernels.cubin\n"
  "heldout_device_ptx=<CUDA_COMPILER> ${R35_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r35_heldout_trace_rebase_kernels.cu -o <BUILD>/generated/r35_heldout_trace_rebase_kernels.ptx\n"
  "heldout_device_cubin=<CUDA_COMPILER> ${R35_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r35_heldout_trace_rebase_kernels.cu -o <BUILD>/generated/r35_heldout_trace_rebase_kernels.cubin\n"
  "checker_discovery=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R35_TRACE_CHARACTER_REBASES.olean <BUILD>/artifacts/R35_TRACE_CHARACTER_REBASES.lean\n"
  "checker_application=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R35_HELDOUT_TRACE_REBASE.olean <BUILD>/artifacts/R35_HELDOUT_TRACE_REBASE.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts" "${PROJECT_BINARY_DIR}/receipts")
set(R35_DISC_DEED "${PROJECT_BINARY_DIR}/receipts/R35_TRACE_REBASE_DISCOVERY_DEED.txt")
set(R35_INTERMEDIATE_REST "${PROJECT_BINARY_DIR}/artifacts/R35_TRACE_REBASE.rest")
set(R35_DISC_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R35_TRACE_CHARACTER_REBASES.lean")
set(R35_DISC_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R35_TRACE_CHARACTER_REBASES.olean")
set(R35_DISC_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R35_DISCOVERY_STDOUT.txt")
set(R35_DISC_STDERR "${PROJECT_BINARY_DIR}/artifacts/R35_DISCOVERY_STDERR.txt")
set(R35_STATE_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R35_TRACE_REBASE_STATE_ATLAS.tsv")
set(R35_EDGE_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R35_TRACE_REBASE_EDGE_ATLAS.tsv")
set(R35_TANGENT_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R35_TRACE_REBASE_TANGENT_ATLAS.tsv")
set(R35_LAW_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R35_TRACE_REBASE_LAW_ATLAS.tsv")
set(R35_APP_DEED "${PROJECT_BINARY_DIR}/receipts/R35_TRACE_REBASE_APPLICATION_DEED.txt")
set(R35_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R35_TRACE_REBASE_HANDOFF.rest")
set(R35_APP_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R35_HELDOUT_TRACE_REBASE.lean")
set(R35_APP_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R35_HELDOUT_TRACE_REBASE.olean")
set(R35_APP_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R35_APPLICATION_STDOUT.txt")
set(R35_APP_STDERR "${PROJECT_BINARY_DIR}/artifacts/R35_APPLICATION_STDERR.txt")
set(R35_DOSSIER "${PROJECT_BINARY_DIR}/artifacts/R35_TRACE_REBASE_DOSSIER.md")
set(R35_APP_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R35_HELDOUT_TRACE_REBASE_ATLAS.tsv")
set(R35_SOURCE_AUDIT "${PROJECT_BINARY_DIR}/receipts/R35_SOURCE_ACCESS_AUDIT.txt")
set(R35_HOST_CONFORMANCE "${PROJECT_BINARY_DIR}/receipts/R35_HOST_CONFORMANCE.txt")
set(R35_DETERMINISM "${PROJECT_BINARY_DIR}/receipts/R35_DETERMINISM.txt")
set(R35_SEAL "${PROJECT_BINARY_DIR}/receipts/R35_SEALED_RETURN.txt")
set(R35_LITERATURE_COMPARISON
  "${PROJECT_BINARY_DIR}/artifacts/R35_POST_SEAL_LITERATURE_COMPARISON.md")
include(cmake/R35TraceRebaseTests.cmake)
set(R35_EXTRA_ARTIFACTS "$<TARGET_FILE:r35_trace_rebase_discovery_device_deed>|$<TARGET_FILE:r35_trace_rebase_application_device_deed>|$<TARGET_FILE:r35_trace_rebase_host_conformance>|${R35_DEVICE_PTX}|${R35_DEVICE_CUBIN}|${R35_HELDOUT_DEVICE_PTX}|${R35_HELDOUT_DEVICE_CUBIN}")
set(R35_DEVICE_PTX_LIST "${R35_DEVICE_PTX}|${R35_HELDOUT_DEVICE_PTX}")
set(R35_DEVICE_CUBIN_LIST "${R35_DEVICE_CUBIN}|${R35_HELDOUT_DEVICE_CUBIN}")
