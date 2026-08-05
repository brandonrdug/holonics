find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r33_characteristic_store STATIC apparatus/host/characteristic_card_adapter.cpp
  apparatus/host/characteristic_rest_adapter.cpp)
target_link_libraries(r33_characteristic_store PRIVATE holonics::apparatus holonics_contract_options)
add_library(r33_characteristic_executor STATIC apparatus/host/lean_checker_process.cpp
  apparatus/host/returned_theorem_checker_process.cpp cuda/executor/r33_characteristic_currents.cu
  cuda/executor/r33_characteristic_kernels.cu cuda/executor/r33_heldout_kernels.cu cuda/executor/r33_discovery_executor.cu
  cuda/executor/r33_application_executor.cu)
target_link_libraries(r33_characteristic_executor PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)
add_executable(r33_characteristic_discovery_device_deed apparatus/host/r33_characteristic_discovery_deed.cpp)
target_link_libraries(r33_characteristic_discovery_device_deed PRIVATE holonics::apparatus
  holonics_contract_options r32_elementary_store r33_characteristic_store r33_characteristic_executor CUDA::cudart)
add_executable(r33_characteristic_application_device_deed apparatus/host/r33_characteristic_application_deed.cpp)
target_link_libraries(r33_characteristic_application_device_deed PRIVATE holonics::apparatus
  holonics_contract_options r33_characteristic_store r33_characteristic_executor CUDA::cudart)
add_executable(r33_characteristic_host_conformance
  tests/conformance/r33_characteristic_host_conformance.cpp)
target_link_libraries(r33_characteristic_host_conformance PRIVATE holonics_contract_options)

file(GLOB_RECURSE R33_DEVICE_HEADERS CONFIGURE_DEPENDS "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R33_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r33_characteristic_kernels.cu")
set(R33_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r33_characteristic_kernels.ptx")
set(R33_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r33_characteristic_kernels.cubin")
set(R33_HELDOUT_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r33_heldout_kernels.cu")
set(R33_HELDOUT_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r33_heldout_kernels.ptx")
set(R33_HELDOUT_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r33_heldout_kernels.cubin")
set(R33_DEVICE_COMMON_FLAGS --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/include -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R33_DEVICE_PTX}" COMMAND "${CMAKE_CUDA_COMPILER}" ${R33_DEVICE_COMMON_FLAGS}
  --ptx "${R33_DEVICE_SOURCE}" -o "${R33_DEVICE_PTX}" DEPENDS "${R33_DEVICE_SOURCE}" ${R33_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R33_DEVICE_CUBIN}" COMMAND "${CMAKE_CUDA_COMPILER}" ${R33_DEVICE_COMMON_FLAGS}
  --cubin "${R33_DEVICE_SOURCE}" -o "${R33_DEVICE_CUBIN}" DEPENDS "${R33_DEVICE_SOURCE}" ${R33_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R33_HELDOUT_DEVICE_PTX}" COMMAND "${CMAKE_CUDA_COMPILER}" ${R33_DEVICE_COMMON_FLAGS}
  --ptx "${R33_HELDOUT_DEVICE_SOURCE}" -o "${R33_HELDOUT_DEVICE_PTX}"
  DEPENDS "${R33_HELDOUT_DEVICE_SOURCE}" ${R33_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R33_HELDOUT_DEVICE_CUBIN}" COMMAND "${CMAKE_CUDA_COMPILER}" ${R33_DEVICE_COMMON_FLAGS}
  --cubin "${R33_HELDOUT_DEVICE_SOURCE}" -o "${R33_HELDOUT_DEVICE_CUBIN}"
  DEPENDS "${R33_HELDOUT_DEVICE_SOURCE}" ${R33_DEVICE_HEADERS} VERBATIM)
add_custom_target(r33_device_artifacts ALL DEPENDS ${R33_DEVICE_PTX} ${R33_DEVICE_CUBIN}
  ${R33_HELDOUT_DEVICE_PTX} ${R33_HELDOUT_DEVICE_CUBIN})
string(JOIN " " R33_DEVICE_FLAGS_RECEIPT ${R33_DEVICE_COMMON_FLAGS})
set(R33_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R33_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r33_characteristic_kernels.cu -o <BUILD>/generated/r33_characteristic_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R33_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r33_characteristic_kernels.cu -o <BUILD>/generated/r33_characteristic_kernels.cubin\n"
  "heldout_device_ptx=<CUDA_COMPILER> ${R33_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r33_heldout_kernels.cu -o <BUILD>/generated/r33_heldout_kernels.ptx\n"
  "heldout_device_cubin=<CUDA_COMPILER> ${R33_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r33_heldout_kernels.cu -o <BUILD>/generated/r33_heldout_kernels.cubin\n"
  "checker_discovery=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R33_CHARACTERISTIC_HYPERGEOMETRY.olean <BUILD>/artifacts/R33_CHARACTERISTIC_HYPERGEOMETRY.lean\n"
  "checker_application=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R33_HELDOUT_CHARACTERISTIC.olean <BUILD>/artifacts/R33_HELDOUT_CHARACTERISTIC.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts" "${PROJECT_BINARY_DIR}/receipts")
set(R33_DISC_DEED "${PROJECT_BINARY_DIR}/receipts/R33_CHARACTERISTIC_DISCOVERY_DEED.txt")
set(R33_INTERMEDIATE_REST "${PROJECT_BINARY_DIR}/artifacts/R33_CHARACTERISTIC_HYPERGEOMETRY.rest")
set(R33_DISC_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R33_CHARACTERISTIC_HYPERGEOMETRY.lean")
set(R33_DISC_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R33_CHARACTERISTIC_HYPERGEOMETRY.olean")
set(R33_DISC_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R33_DISCOVERY_STDOUT.txt")
set(R33_DISC_STDERR "${PROJECT_BINARY_DIR}/artifacts/R33_DISCOVERY_STDERR.txt")
set(R33_WORD_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R33_TRANSITION_WORD_ATLAS.tsv")
set(R33_PAIR_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R33_CHARACTERISTIC_PAIR_ATLAS.tsv")
set(R33_GROUP_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R33_ARCHETYPE_GROUP_ATLAS.tsv")
set(R33_LAW_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R33_TRACE_LAW_ATLAS.tsv")
set(R33_APP_DEED "${PROJECT_BINARY_DIR}/receipts/R33_CHARACTERISTIC_APPLICATION_DEED.txt")
set(R33_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R33_CHARACTERISTIC_TRANSPORT_HANDOFF.rest")
set(R33_APP_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R33_HELDOUT_CHARACTERISTIC.lean")
set(R33_APP_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R33_HELDOUT_CHARACTERISTIC.olean")
set(R33_APP_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R33_APPLICATION_STDOUT.txt")
set(R33_APP_STDERR "${PROJECT_BINARY_DIR}/artifacts/R33_APPLICATION_STDERR.txt")
set(R33_DOSSIER "${PROJECT_BINARY_DIR}/artifacts/R33_CHARACTERISTIC_HYPERGEOMETRY_DOSSIER.md")
set(R33_APP_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R33_HELDOUT_CHARACTERISTIC_ATLAS.tsv")
set(R33_SOURCE_AUDIT "${PROJECT_BINARY_DIR}/receipts/R33_SOURCE_ACCESS_AUDIT.txt")
set(R33_HOST_CONFORMANCE "${PROJECT_BINARY_DIR}/receipts/R33_HOST_CONFORMANCE.txt")
set(R33_DETERMINISM "${PROJECT_BINARY_DIR}/receipts/R33_DETERMINISM.txt")
set(R33_SEAL "${PROJECT_BINARY_DIR}/receipts/R33_SEALED_RETURN.txt")
set(R33_LITERATURE_COMPARISON
  "${PROJECT_BINARY_DIR}/artifacts/R33_POST_SEAL_LITERATURE_COMPARISON.md")
include(cmake/R33CharacteristicTests.cmake)

set(R33_EXTRA_ARTIFACTS "$<TARGET_FILE:r33_characteristic_discovery_device_deed>|$<TARGET_FILE:r33_characteristic_application_device_deed>|$<TARGET_FILE:r33_characteristic_host_conformance>|${R33_DEVICE_PTX}|${R33_DEVICE_CUBIN}|${R33_HELDOUT_DEVICE_PTX}|${R33_HELDOUT_DEVICE_CUBIN}")
set(R33_DEVICE_PTX_LIST "${R33_DEVICE_PTX}|${R33_HELDOUT_DEVICE_PTX}")
set(R33_DEVICE_CUBIN_LIST "${R33_DEVICE_CUBIN}|${R33_HELDOUT_DEVICE_CUBIN}")
