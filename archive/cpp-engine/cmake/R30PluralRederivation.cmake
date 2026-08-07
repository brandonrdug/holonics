find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r30_rederivation_store STATIC
  src/apparatus/host/rederivation_card_adapter.cpp
  src/apparatus/host/rederivation_store_adapter.cpp)
target_link_libraries(r30_rederivation_store
  PRIVATE holonics::apparatus holonics_contract_options)

add_library(r30_rederivation_executor STATIC
  src/apparatus/host/lean_checker_process.cpp
  src/cuda/executor/r30_rederivation_currents.cu
  src/cuda/executor/r30_rederivation_executor.cu
  src/cuda/executor/r30_rederivation_kernels.cu)
target_link_libraries(r30_rederivation_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r30_plural_rederivation_device_deed
  src/apparatus/host/r30_rederivation_deed.cpp
  tests/model/r30_artifact.cpp tests/model/r30_atlas.cpp tests/model/r30_cases.cpp
  tests/model/r30_reference.cpp tests/model/r30_reference_field.cpp
  tests/model/r30_verify.cpp)
target_include_directories(r30_plural_rederivation_device_deed
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r30_plural_rederivation_device_deed PRIVATE holonics::apparatus
  holonics_contract_options r30_rederivation_store r30_rederivation_executor CUDA::cudart)

add_executable(r30_rederivation_host_conformance
  tests/conformance/r30_rederivation_host_conformance.cpp
  tests/model/r30_cases.cpp tests/model/r30_reference.cpp)
target_include_directories(r30_rederivation_host_conformance
  PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r30_rederivation_host_conformance
  PRIVATE holonics::event holonics_contract_options CUDA::cudart)

add_library(r30_open_probe SHARED tests/apparatus/r30_open_probe.cpp)
target_link_libraries(r30_open_probe PRIVATE holonics_contract_options)
set_target_properties(r30_open_probe PROPERTIES PREFIX "")

add_custom_target(r30_normalize_executable
  COMMAND /usr/bin/objcopy --strip-unneeded $<TARGET_FILE:r30_plural_rederivation_device_deed>
  DEPENDS r30_plural_rederivation_device_deed VERBATIM)

file(GLOB_RECURSE R30_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/*.hpp")
set(R30_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/r30_rederivation_kernels.cu")
set(R30_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r30_rederivation_kernels.ptx")
set(R30_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r30_rederivation_kernels.cubin")
set(R30_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/src/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R30_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R30_DEVICE_COMMON_FLAGS} --ptx
    "${R30_DEVICE_SOURCE}" -o "${R30_DEVICE_PTX}"
  DEPENDS "${R30_DEVICE_SOURCE}" ${R30_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R30_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R30_DEVICE_COMMON_FLAGS} --cubin
    "${R30_DEVICE_SOURCE}" -o "${R30_DEVICE_CUBIN}"
  DEPENDS "${R30_DEVICE_SOURCE}" ${R30_DEVICE_HEADERS} VERBATIM)
add_custom_target(r30_device_artifacts ALL DEPENDS ${R30_DEVICE_PTX} ${R30_DEVICE_CUBIN})

string(JOIN " " R30_DEVICE_FLAGS_RECEIPT ${R30_DEVICE_COMMON_FLAGS})
set(R30_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R30_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r30_rederivation_kernels.cu -o <BUILD>/generated/r30_rederivation_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R30_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r30_rederivation_kernels.cu -o <BUILD>/generated/r30_rederivation_kernels.cubin\n"
  "checker_foil=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R30_REJECTED_FOIL.olean <BUILD>/artifacts/R30_REJECTED_FOIL.lean\n"
  "checker_valid=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R30_GENERATED_PLURAL_REDERIVATION.olean <BUILD>/artifacts/R30_GENERATED_PLURAL_REDERIVATION.lean\n"
  "source_access=LD_PRELOAD=<BUILD>/r30_open_probe.so <BUILD>/r30_plural_rederivation_device_deed <R30_ARGUMENTS>\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts" "${PROJECT_BINARY_DIR}/receipts")
set(R30_DEED_ARTIFACT "${PROJECT_BINARY_DIR}/receipts/R30_PLURAL_REDERIVATION_DEED.txt")
set(R30_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R30_PLURAL_REDERIVATION_HANDOFF.rest")
set(R30_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R30_GENERATED_PLURAL_REDERIVATION.lean")
set(R30_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R30_GENERATED_PLURAL_REDERIVATION.olean")
set(R30_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R30_LEAN_STDOUT.txt")
set(R30_STDERR "${PROJECT_BINARY_DIR}/artifacts/R30_LEAN_STDERR.txt")
set(R30_FOIL_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R30_REJECTED_FOIL.lean")
set(R30_FOIL_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R30_REJECTED_FOIL.olean")
set(R30_FOIL_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R30_FOIL_STDOUT.txt")
set(R30_FOIL_STDERR "${PROJECT_BINARY_DIR}/artifacts/R30_FOIL_STDERR.txt")
set(R30_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R30_REDERIVATION_ATLAS.tsv")
set(R30_DOSSIER "${PROJECT_BINARY_DIR}/artifacts/R30_REDERIVATION_DOSSIER.md")
set(R30_OPEN_LOG "${PROJECT_BINARY_DIR}/artifacts/R30_OPEN_PATHS.txt")
set(R30_SOURCE_AUDIT "${PROJECT_BINARY_DIR}/receipts/R30_SOURCE_ACCESS_AUDIT.txt")
set(R30_SEAL_MANIFEST "${PROJECT_BINARY_DIR}/receipts/R30_SEALED_RETURN.txt")
set(R30_COMPARISON "${PROJECT_BINARY_DIR}/artifacts/R30_POST_SEAL_COMPARISON.md")
# The foil is a proof the kernel is SUPPOSED to refuse, so no object is ever
# produced at this path. Its absence is the deed's negative control and must not
# be read as work left undone by any founding that names it.
holonic_withhold("${R30_FOIL_OLEAN}")

holonic_found(NAME r30.plural_rederivation_device_deed
  EXECUTABLE r30_plural_rederivation_device_deed
  COMMAND
    "${R30_DEED_ARTIFACT}" "${R29_FINAL_REST}" "${R30_FINAL_REST}"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R30_MATCHING_JACOBIAN.card"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R30_LATTICE_POTENTIAL.card"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R30_COORDINATE_COVER.card" "${R30_SOURCE}"
    "${R30_OLEAN}" "${R30_STDOUT}" "${R30_STDERR}" "${R30_FOIL_SOURCE}" "${R30_FOIL_OLEAN}"
    "${R30_FOIL_STDOUT}" "${R30_FOIL_STDERR}"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R30_ATLAS}" "${R30_DOSSIER}")
holonic_found(NAME r30.source_access_audit
  COMMAND
    "${CMAKE_COMMAND}" -DEXECUTABLE=$<TARGET_FILE:r30_plural_rederivation_device_deed>
    -DPROBE=$<TARGET_FILE:r30_open_probe> -DLOG=${R30_OPEN_LOG} -DOUTPUT=${R30_SOURCE_AUDIT}
    -DSOURCE_ROOT=${PROJECT_SOURCE_DIR} -DDEED=${R30_DEED_ARTIFACT}
    -DPREDECESSOR=${R29_FINAL_REST} -DHANDOFF=${R30_FINAL_REST}
    -DMATCHING=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R30_MATCHING_JACOBIAN.card
    -DLATTICE=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R30_LATTICE_POTENTIAL.card
    -DCOVER=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R30_COORDINATE_COVER.card
    -DSOURCE=${R30_SOURCE} -DOLEAN=${R30_OLEAN} -DSTDOUT=${R30_STDOUT}
    -DSTDERR=${R30_STDERR} -DFOIL_SOURCE=${R30_FOIL_SOURCE} -DFOIL_OLEAN=${R30_FOIL_OLEAN}
    -DFOIL_STDOUT=${R30_FOIL_STDOUT} -DFOIL_STDERR=${R30_FOIL_STDERR}
    -DFORMAL_ROOT=${PROJECT_SOURCE_DIR}/formal/elementary-holonics
    -DTOOLCHAIN=${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain
    -DMANIFEST=${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json
    -DARTIFACT_ROOT=${PROJECT_BINARY_DIR}/artifacts -DATLAS=${R30_ATLAS}
    -DDOSSIER=${R30_DOSSIER} -P "${PROJECT_SOURCE_DIR}/cmake/R30SourceAccessAudit.cmake")
add_test(NAME r30.seal_and_compare COMMAND "${CMAKE_COMMAND}"
  -DOUTPUT=${R30_SEAL_MANIFEST} -DCOMPARISON=${R30_COMPARISON}
  -DSOURCE_AUDIT=${R30_SOURCE_AUDIT} -DDEED=${R30_DEED_ARTIFACT}
  -DREST=${R30_FINAL_REST} -DSOURCE=${R30_SOURCE} -DOLEAN=${R30_OLEAN}
  -DFOIL_SOURCE=${R30_FOIL_SOURCE} -DFOIL_STDOUT=${R30_FOIL_STDOUT}
  -DATLAS=${R30_ATLAS} -DDOSSIER=${R30_DOSSIER}
  -P "${PROJECT_SOURCE_DIR}/cmake/R30SealComparison.cmake")
set_tests_properties(r30.seal_and_compare PROPERTIES DEPENDS "r30.source_access_audit")
holonic_found(NAME r30.rederivation_host_conformance
  EXECUTABLE r30_rederivation_host_conformance
  COMMAND
   )
add_test(NAME r30.forbidden_rederivation_copy COMMAND "${CMAKE_COMMAND}"
  -DCOMPILER=${CMAKE_CXX_COMPILER}
  -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_rederivation_copy.cpp
  -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/src/include
  "-DEXPECTED_TEXT=use of deleted function"
  -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R30_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r30_plural_rederivation_device_deed>|${R30_DEVICE_PTX}|${R30_DEVICE_CUBIN}")
set(R30_DEVICE_PTX_LIST "${R30_DEVICE_PTX}")
set(R30_DEVICE_CUBIN_LIST "${R30_DEVICE_CUBIN}")
