find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r17_geometry_inquiry_store STATIC
  apparatus/host/geometry_inquiry_store_adapter.cpp
  apparatus/host/sealed_geometry_reference_adapter.cpp)
target_link_libraries(r17_geometry_inquiry_store
  PRIVATE holonics::apparatus holonics_contract_options)

add_library(r17_geometry_inquiry_executor STATIC
  apparatus/host/lean_checker_process.cpp
  cuda/executor/r17_geometry_inquiry_executor.cu
  cuda/executor/r17_geometry_inquiry_kernels.cu)
target_link_libraries(r17_geometry_inquiry_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r17_agnostic_geometry_inquiry_device_deed
  apparatus/host/r17_agnostic_geometry_inquiry_deed.cpp
  tests/model/r17_artifact.cpp
  tests/model/r17_cases.cpp
  tests/model/r17_verify.cpp)
target_include_directories(r17_agnostic_geometry_inquiry_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r17_agnostic_geometry_inquiry_device_deed
  PRIVATE holonics::apparatus holonics_contract_options r17_geometry_inquiry_store
    r17_geometry_inquiry_executor CUDA::cudart)

add_executable(r17_geometry_inquiry_host_conformance
  tests/conformance/r17_geometry_inquiry_host_conformance.cpp
  tests/model/r17_cases.cpp)
target_include_directories(r17_geometry_inquiry_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r17_geometry_inquiry_host_conformance
  PRIVATE holonics::event holonics_contract_options)

add_custom_target(r17_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded
    $<TARGET_FILE:r17_agnostic_geometry_inquiry_device_deed>
  DEPENDS r17_agnostic_geometry_inquiry_device_deed VERBATIM)

file(GLOB_RECURSE R17_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/include/holonics/*.hpp")
set(R17_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/cuda/executor/r17_geometry_inquiry_kernels.cu")
set(R17_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r17_geometry_inquiry_kernels.ptx")
set(R17_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r17_geometry_inquiry_kernels.cubin")
set(R17_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R17_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R17_DEVICE_COMMON_FLAGS} --ptx
    "${R17_DEVICE_SOURCE}" -o "${R17_DEVICE_PTX}"
  DEPENDS "${R17_DEVICE_SOURCE}" ${R17_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R17_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R17_DEVICE_COMMON_FLAGS} --cubin
    "${R17_DEVICE_SOURCE}" -o "${R17_DEVICE_CUBIN}"
  DEPENDS "${R17_DEVICE_SOURCE}" ${R17_DEVICE_HEADERS} VERBATIM)
add_custom_target(r17_device_artifacts ALL DEPENDS ${R17_DEVICE_PTX} ${R17_DEVICE_CUBIN})

string(JOIN " " R17_DEVICE_FLAGS_RECEIPT ${R17_DEVICE_COMMON_FLAGS})
set(R17_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R17_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/cuda/executor/r17_geometry_inquiry_kernels.cu -o <BUILD>/generated/r17_geometry_inquiry_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R17_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/cuda/executor/r17_geometry_inquiry_kernels.cu -o <BUILD>/generated/r17_geometry_inquiry_kernels.cubin\n"
  "exterior_checker=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R17_GENERATED_GEOMETRY.olean <BUILD>/artifacts/R17_GENERATED_GEOMETRY.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts")
set(R17_DEED_ARTIFACT
  "${PROJECT_BINARY_DIR}/receipts/R17_AGNOSTIC_GEOMETRY_INQUIRY_DEED.txt")
set(R17_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R17_GEOMETRY_INQUIRY_HANDOFF.rest")
set(R17_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R17_GENERATED_GEOMETRY.lean")
set(R17_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R17_GENERATED_GEOMETRY.olean")
set(R17_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R17_LEAN_STDOUT.txt")
set(R17_STDERR "${PROJECT_BINARY_DIR}/artifacts/R17_LEAN_STDERR.txt")
add_test(NAME r17.agnostic_geometry_inquiry_device_deed
  COMMAND r17_agnostic_geometry_inquiry_device_deed "${R17_DEED_ARTIFACT}"
    "${R16_FINAL_REST}" "${R17_FINAL_REST}" "${R17_SOURCE}" "${R17_OLEAN}"
    "${R17_STDOUT}" "${R17_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/ElementaryHolonics/Geometry/CrossRatio.lean")
set_tests_properties(r17.agnostic_geometry_inquiry_device_deed PROPERTIES
  DEPENDS "r16.two_theorem_conversational_device_deed")
add_test(NAME r17.geometry_inquiry_host_conformance
  COMMAND r17_geometry_inquiry_host_conformance)
add_test(NAME r17.forbidden_geometry_inquiry_copy
  COMMAND "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_geometry_inquiry_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/include
    "-DEXPECTED_TEXT=use of deleted function"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R17_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r17_agnostic_geometry_inquiry_device_deed>|${R17_DEVICE_PTX}|${R17_DEVICE_CUBIN}")
set(R17_DEVICE_PTX_LIST "${R17_DEVICE_PTX}")
set(R17_DEVICE_CUBIN_LIST "${R17_DEVICE_CUBIN}")
