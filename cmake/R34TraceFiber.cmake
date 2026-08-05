find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r34_trace_fiber_store STATIC apparatus/host/trace_fiber_card_adapter.cpp
  apparatus/host/trace_fiber_rest_adapter.cpp)
target_link_libraries(r34_trace_fiber_store PRIVATE holonics::apparatus holonics_contract_options)
add_library(r34_trace_fiber_executor STATIC apparatus/host/lean_checker_process.cpp
  apparatus/host/returned_theorem_checker_process.cpp cuda/executor/r34_trace_fiber_currents.cu
  cuda/executor/r34_trace_fiber_kernels.cu cuda/executor/r34_heldout_trace_fiber_kernels.cu
  cuda/executor/r34_trace_fiber_discovery_executor.cu
  cuda/executor/r34_trace_fiber_application_executor.cu)
target_link_libraries(r34_trace_fiber_executor PRIVATE holonics::apparatus
  holonics_contract_options CUDA::cudart)
add_executable(r34_trace_fiber_discovery_device_deed
  apparatus/host/r34_trace_fiber_discovery_deed.cpp)
target_link_libraries(r34_trace_fiber_discovery_device_deed PRIVATE holonics::apparatus
  holonics_contract_options r33_characteristic_store r34_trace_fiber_store
  r34_trace_fiber_executor CUDA::cudart)
add_executable(r34_trace_fiber_application_device_deed
  apparatus/host/r34_trace_fiber_application_deed.cpp)
target_link_libraries(r34_trace_fiber_application_device_deed PRIVATE holonics::apparatus
  holonics_contract_options r34_trace_fiber_store r34_trace_fiber_executor CUDA::cudart)
add_executable(r34_trace_fiber_host_conformance
  tests/conformance/r34_trace_fiber_host_conformance.cpp)
target_link_libraries(r34_trace_fiber_host_conformance PRIVATE holonics_contract_options)

file(GLOB_RECURSE R34_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R34_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r34_trace_fiber_kernels.cu")
set(R34_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r34_trace_fiber_kernels.ptx")
set(R34_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r34_trace_fiber_kernels.cubin")
set(R34_HELDOUT_DEVICE_SOURCE
  "${PROJECT_SOURCE_DIR}/cuda/executor/r34_heldout_trace_fiber_kernels.cu")
set(R34_HELDOUT_DEVICE_PTX
  "${R0_GENERATED_DIRECTORY}/r34_heldout_trace_fiber_kernels.ptx")
set(R34_HELDOUT_DEVICE_CUBIN
  "${R0_GENERATED_DIRECTORY}/r34_heldout_trace_fiber_kernels.cubin")
set(R34_DEVICE_COMMON_FLAGS --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false
  --Werror=all-warnings -I${PROJECT_SOURCE_DIR}/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R34_DEVICE_PTX}" COMMAND "${CMAKE_CUDA_COMPILER}"
  ${R34_DEVICE_COMMON_FLAGS} --ptx "${R34_DEVICE_SOURCE}" -o "${R34_DEVICE_PTX}"
  DEPENDS "${R34_DEVICE_SOURCE}" ${R34_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R34_DEVICE_CUBIN}" COMMAND "${CMAKE_CUDA_COMPILER}"
  ${R34_DEVICE_COMMON_FLAGS} --cubin "${R34_DEVICE_SOURCE}" -o "${R34_DEVICE_CUBIN}"
  DEPENDS "${R34_DEVICE_SOURCE}" ${R34_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R34_HELDOUT_DEVICE_PTX}" COMMAND "${CMAKE_CUDA_COMPILER}"
  ${R34_DEVICE_COMMON_FLAGS} --ptx "${R34_HELDOUT_DEVICE_SOURCE}"
  -o "${R34_HELDOUT_DEVICE_PTX}" DEPENDS "${R34_HELDOUT_DEVICE_SOURCE}"
  ${R34_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R34_HELDOUT_DEVICE_CUBIN}" COMMAND "${CMAKE_CUDA_COMPILER}"
  ${R34_DEVICE_COMMON_FLAGS} --cubin "${R34_HELDOUT_DEVICE_SOURCE}"
  -o "${R34_HELDOUT_DEVICE_CUBIN}" DEPENDS "${R34_HELDOUT_DEVICE_SOURCE}"
  ${R34_DEVICE_HEADERS} VERBATIM)
add_custom_target(r34_device_artifacts ALL DEPENDS ${R34_DEVICE_PTX} ${R34_DEVICE_CUBIN}
  ${R34_HELDOUT_DEVICE_PTX} ${R34_HELDOUT_DEVICE_CUBIN})
string(JOIN " " R34_DEVICE_FLAGS_RECEIPT ${R34_DEVICE_COMMON_FLAGS})
set(R34_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R34_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r34_trace_fiber_kernels.cu -o <BUILD>/generated/r34_trace_fiber_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R34_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r34_trace_fiber_kernels.cu -o <BUILD>/generated/r34_trace_fiber_kernels.cubin\n"
  "heldout_device_ptx=<CUDA_COMPILER> ${R34_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r34_heldout_trace_fiber_kernels.cu -o <BUILD>/generated/r34_heldout_trace_fiber_kernels.ptx\n"
  "heldout_device_cubin=<CUDA_COMPILER> ${R34_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r34_heldout_trace_fiber_kernels.cu -o <BUILD>/generated/r34_heldout_trace_fiber_kernels.cubin\n"
  "checker_discovery=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R34_TRACE_FIBER_LIFTING.olean <BUILD>/artifacts/R34_TRACE_FIBER_LIFTING.lean\n"
  "checker_application=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R34_HELDOUT_TRACE_FIBER.olean <BUILD>/artifacts/R34_HELDOUT_TRACE_FIBER.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts" "${PROJECT_BINARY_DIR}/receipts")
set(R34_DISC_DEED "${PROJECT_BINARY_DIR}/receipts/R34_TRACE_FIBER_DISCOVERY_DEED.txt")
set(R34_INTERMEDIATE_REST "${PROJECT_BINARY_DIR}/artifacts/R34_TRACE_FIBER_LIFTING.rest")
set(R34_DISC_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R34_TRACE_FIBER_LIFTING.lean")
set(R34_DISC_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R34_TRACE_FIBER_LIFTING.olean")
set(R34_DISC_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R34_DISCOVERY_STDOUT.txt")
set(R34_DISC_STDERR "${PROJECT_BINARY_DIR}/artifacts/R34_DISCOVERY_STDERR.txt")
set(R34_WORD_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R34_TRANSITION_WORD_ATLAS.tsv")
set(R34_TRIPLE_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R34_TRACE_FIBER_TRIPLE_ATLAS.tsv")
set(R34_GROUP_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R34_TRACE_FIBER_GROUP_ATLAS.tsv")
set(R34_LAW_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R34_TRACE_FIBER_LAW_ATLAS.tsv")
set(R34_APP_DEED "${PROJECT_BINARY_DIR}/receipts/R34_TRACE_FIBER_APPLICATION_DEED.txt")
set(R34_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R34_TRACE_FIBER_HANDOFF.rest")
set(R34_APP_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R34_HELDOUT_TRACE_FIBER.lean")
set(R34_APP_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R34_HELDOUT_TRACE_FIBER.olean")
set(R34_APP_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R34_APPLICATION_STDOUT.txt")
set(R34_APP_STDERR "${PROJECT_BINARY_DIR}/artifacts/R34_APPLICATION_STDERR.txt")
set(R34_DOSSIER "${PROJECT_BINARY_DIR}/artifacts/R34_TRACE_FIBER_DOSSIER.md")
set(R34_APP_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R34_HELDOUT_TRACE_FIBER_ATLAS.tsv")
set(R34_SOURCE_AUDIT "${PROJECT_BINARY_DIR}/receipts/R34_SOURCE_ACCESS_AUDIT.txt")
set(R34_HOST_CONFORMANCE "${PROJECT_BINARY_DIR}/receipts/R34_HOST_CONFORMANCE.txt")
set(R34_DETERMINISM "${PROJECT_BINARY_DIR}/receipts/R34_DETERMINISM.txt")
set(R34_SEAL "${PROJECT_BINARY_DIR}/receipts/R34_SEALED_RETURN.txt")
set(R34_LITERATURE_COMPARISON
  "${PROJECT_BINARY_DIR}/artifacts/R34_POST_SEAL_LITERATURE_COMPARISON.md")
include(cmake/R34TraceFiberTests.cmake)

set(R34_EXTRA_ARTIFACTS "$<TARGET_FILE:r34_trace_fiber_discovery_device_deed>|$<TARGET_FILE:r34_trace_fiber_application_device_deed>|$<TARGET_FILE:r34_trace_fiber_host_conformance>|${R34_DEVICE_PTX}|${R34_DEVICE_CUBIN}|${R34_HELDOUT_DEVICE_PTX}|${R34_HELDOUT_DEVICE_CUBIN}")
set(R34_DEVICE_PTX_LIST "${R34_DEVICE_PTX}|${R34_HELDOUT_DEVICE_PTX}")
set(R34_DEVICE_CUBIN_LIST "${R34_DEVICE_CUBIN}|${R34_HELDOUT_DEVICE_CUBIN}")
