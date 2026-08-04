find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r19_characteristic_store STATIC
  apparatus/host/characteristic_store_adapter.cpp)
target_link_libraries(r19_characteristic_store
  PRIVATE holonics::apparatus holonics_contract_options)

add_library(r19_characteristic_executor STATIC
  apparatus/host/lean_checker_process.cpp
  cuda/executor/r19_characteristic_executor.cu
  cuda/executor/r19_characteristic_kernels.cu)
target_link_libraries(r19_characteristic_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r19_characteristic_device_deed
  apparatus/host/r19_characteristic_deed.cpp
  tests/model/r19_artifact.cpp
  tests/model/r19_cases.cpp
  tests/model/r19_verify.cpp)
target_include_directories(r19_characteristic_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r19_characteristic_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r19_characteristic_store
    r19_characteristic_executor CUDA::cudart)

add_executable(r19_characteristic_host_conformance
  tests/conformance/r19_characteristic_host_conformance.cpp
  tests/model/r19_cases.cpp)
target_include_directories(r19_characteristic_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r19_characteristic_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r19_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r19_characteristic_device_deed>
  DEPENDS r19_characteristic_device_deed VERBATIM)

file(GLOB_RECURSE R19_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R19_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r19_characteristic_kernels.cu")
set(R19_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r19_characteristic_kernels.ptx")
set(R19_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r19_characteristic_kernels.cubin")
set(R19_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R19_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R19_DEVICE_COMMON_FLAGS} --ptx
    "${R19_DEVICE_SOURCE}" -o "${R19_DEVICE_PTX}"
  DEPENDS "${R19_DEVICE_SOURCE}" ${R19_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R19_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R19_DEVICE_COMMON_FLAGS} --cubin
    "${R19_DEVICE_SOURCE}" -o "${R19_DEVICE_CUBIN}"
  DEPENDS "${R19_DEVICE_SOURCE}" ${R19_DEVICE_HEADERS} VERBATIM)
add_custom_target(r19_device_artifacts ALL DEPENDS ${R19_DEVICE_PTX} ${R19_DEVICE_CUBIN})

string(JOIN " " R19_DEVICE_FLAGS_RECEIPT ${R19_DEVICE_COMMON_FLAGS})
set(R19_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R19_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r19_characteristic_kernels.cu -o <BUILD>/generated/r19_characteristic_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R19_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r19_characteristic_kernels.cu -o <BUILD>/generated/r19_characteristic_kernels.cubin\n"
  "exterior_checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R19_GENERATED_CHARACTERISTIC.olean <BUILD>/artifacts/R19_GENERATED_CHARACTERISTIC.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts")
set(R19_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R19_CHARACTERISTIC_DEED.txt")
set(R19_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R19_CHARACTERISTIC_HANDOFF.rest")
set(R19_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R19_GENERATED_CHARACTERISTIC.lean")
set(R19_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R19_GENERATED_CHARACTERISTIC.olean")
set(R19_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R19_LEAN_STDOUT.txt")
set(R19_STDERR "${PROJECT_BINARY_DIR}/artifacts/R19_LEAN_STDERR.txt")
set(R19_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R19_CHARACTERISTIC_ATLAS.tsv")
add_test(NAME r19.characteristic_device_deed
  COMMAND r19_characteristic_device_deed "${R19_DEED_ARTIFACT}"
    "${R18_FINAL_REST}" "${R19_FINAL_REST}" "${R19_SOURCE}" "${R19_OLEAN}"
    "${R19_STDOUT}" "${R19_STDERR}" "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R19_ATLAS}")
set_tests_properties(r19.characteristic_device_deed PROPERTIES
  DEPENDS "r18.phase_crystal_device_deed")
add_test(NAME r19.characteristic_host_conformance COMMAND r19_characteristic_host_conformance)
add_test(NAME r19.forbidden_characteristic_copy
  COMMAND "${CMAKE_COMMAND}" -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_characteristic_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R19_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r19_characteristic_device_deed>|${R19_DEVICE_PTX}|${R19_DEVICE_CUBIN}")
set(R19_DEVICE_PTX_LIST "${R19_DEVICE_PTX}")
set(R19_DEVICE_CUBIN_LIST "${R19_DEVICE_CUBIN}")
