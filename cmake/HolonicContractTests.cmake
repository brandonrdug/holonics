add_test(NAME r0.valid_host_contract COMMAND r0_host_contract)

add_test(
  NAME r0.forbidden_copy_contracts
  COMMAND
    "${CMAKE_COMMAND}"
    -DCOMPILER=${CMAKE_CXX_COMPILER}
    -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_copy.cpp
    -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/src/include
    "-DEXPECTED_TEXT=must not be copy constructible"
    -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

foreach(fixture IN ITEMS float dependency compatibility ownership)
  add_test(
    NAME r0.forbidden_${fixture}_audit
    COMMAND
      "${CMAKE_COMMAND}"
      -DSOURCE_ROOT=${PROJECT_SOURCE_DIR}
      -DSCAN_ROOT=${PROJECT_SOURCE_DIR}/tests/audit_fixtures/${fixture}
      "-DEXPECTED_TEXT=${fixture}"
      -P "${PROJECT_SOURCE_DIR}/cmake/ExpectAuditFailure.cmake")
endforeach()

add_test(
  NAME r0.architecture_and_binary_audit
  COMMAND
    "${CMAKE_COMMAND}"
    -DSOURCE_ROOT=${PROJECT_SOURCE_DIR}
    -DBUILD_ROOT=${PROJECT_BINARY_DIR}
    -DMANIFEST=${HOLONICS_BUILD_MANIFEST}
    -DHOST_BINARY=$<TARGET_FILE:r0_host_contract>
    -DDEVICE_OBJECT=$<TARGET_OBJECTS:r0_device_contract>
    -DDEVICE_PTX=${R0_GENERATED_DIRECTORY}/r0_device_contract.ptx
    -DDEVICE_CUBIN=${R0_GENERATED_DIRECTORY}/r0_device_contract.cubin
    "-DEXTRA_ARTIFACTS=${HOLONICS_EXTRA_ARTIFACTS}"
    "-DEXTRA_DEVICE_PTX=${HOLONICS_EXTRA_DEVICE_PTX}"
    "-DEXTRA_DEVICE_CUBIN=${HOLONICS_EXTRA_DEVICE_CUBIN}"
    -P "${PROJECT_SOURCE_DIR}/cmake/HolonicAudit.cmake")
