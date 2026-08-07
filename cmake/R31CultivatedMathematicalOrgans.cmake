find_package(CUDAToolkit 13.2.78 EXACT REQUIRED)

add_library(r31_cultivated_store STATIC
  src/apparatus/host/cultivated_card_adapter.cpp
  src/apparatus/host/cultivated_rest_adapter.cpp)
target_link_libraries(r31_cultivated_store PRIVATE holonics::apparatus holonics_contract_options)

add_library(r31_cultivated_executor STATIC
  src/apparatus/host/lean_checker_process.cpp
  src/cuda/executor/r31_cultivated_currents.cu
  src/cuda/executor/r31_cultivated_kernels.cu
  src/cuda/executor/r31_cultivation_executor.cu
  src/cuda/executor/r31_application_executor.cu)
target_link_libraries(r31_cultivated_executor
  PRIVATE holonics::apparatus holonics_contract_options CUDA::cudart)

add_executable(r31_organ_cultivation_device_deed
  src/apparatus/host/r31_organ_cultivation_deed.cpp)
target_link_libraries(r31_organ_cultivation_device_deed PRIVATE holonics::apparatus
  holonics_contract_options r30_rederivation_store r31_cultivated_store
  r31_cultivated_executor CUDA::cudart)

add_executable(r31_cultivated_application_device_deed
  src/apparatus/host/r31_cultivated_application_deed.cpp)
target_link_libraries(r31_cultivated_application_device_deed PRIVATE holonics::apparatus
  holonics_contract_options r31_cultivated_store r31_cultivated_executor CUDA::cudart)

add_executable(r31_cultivated_host_conformance
  tests/conformance/r31_cultivated_host_conformance.cpp
  tests/model/r31_host_cards.cpp tests/model/r31_host_reference.cpp
  tests/model/r31_host_heldout.cpp)
target_include_directories(r31_cultivated_host_conformance PRIVATE "${PROJECT_SOURCE_DIR}/tests/model")
target_link_libraries(r31_cultivated_host_conformance
  PRIVATE holonics::event holonics_contract_options CUDA::cudart)

file(GLOB_RECURSE R31_DEVICE_HEADERS CONFIGURE_DEPENDS
  "${PROJECT_SOURCE_DIR}/src/include/holonics/*.hpp")
set(R31_DEVICE_SOURCE "${PROJECT_SOURCE_DIR}/src/cuda/executor/r31_cultivated_kernels.cu")
set(R31_DEVICE_PTX "${R0_GENERATED_DIRECTORY}/r31_cultivated_kernels.ptx")
set(R31_DEVICE_CUBIN "${R0_GENERATED_DIRECTORY}/r31_cultivated_kernels.cubin")
set(R31_DEVICE_COMMON_FLAGS
  --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false --Werror=all-warnings
  -I${PROJECT_SOURCE_DIR}/src/include
  -Xcompiler=-Wall,-Wextra,-Werror,-Wconversion,-Wsign-conversion,-Wshadow,-fno-exceptions,-fno-rtti,-fno-fast-math,-ffp-contract=off,-ffile-prefix-map=${PROJECT_SOURCE_DIR}=.,-ffile-prefix-map=${PROJECT_BINARY_DIR}=.)
add_custom_command(OUTPUT "${R31_DEVICE_PTX}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R31_DEVICE_COMMON_FLAGS} --ptx
    "${R31_DEVICE_SOURCE}" -o "${R31_DEVICE_PTX}"
  DEPENDS "${R31_DEVICE_SOURCE}" ${R31_DEVICE_HEADERS} VERBATIM)
add_custom_command(OUTPUT "${R31_DEVICE_CUBIN}"
  COMMAND "${CMAKE_CUDA_COMPILER}" ${R31_DEVICE_COMMON_FLAGS} --cubin
    "${R31_DEVICE_SOURCE}" -o "${R31_DEVICE_CUBIN}"
  DEPENDS "${R31_DEVICE_SOURCE}" ${R31_DEVICE_HEADERS} VERBATIM)
add_custom_target(r31_device_artifacts ALL DEPENDS ${R31_DEVICE_PTX} ${R31_DEVICE_CUBIN})

string(JOIN " " R31_DEVICE_FLAGS_RECEIPT ${R31_DEVICE_COMMON_FLAGS})
set(R31_DECLARED_COMMANDS
  "device_ptx=<CUDA_COMPILER> ${R31_DEVICE_FLAGS_RECEIPT} --ptx <SOURCE>/src/cuda/executor/r31_cultivated_kernels.cu -o <BUILD>/generated/r31_cultivated_kernels.ptx\n"
  "device_cubin=<CUDA_COMPILER> ${R31_DEVICE_FLAGS_RECEIPT} --cubin <SOURCE>/src/cuda/executor/r31_cultivated_kernels.cu -o <BUILD>/generated/r31_cultivated_kernels.cubin\n"
  "checker_cultivation=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R31_CULTIVATED_ORGANS.olean <BUILD>/artifacts/R31_CULTIVATED_ORGANS.lean\n"
  "checker_application=/usr/bin/lake env lean -R <BUILD>/artifacts -o <BUILD>/artifacts/R31_ORGAN_TRANSPORT.olean <BUILD>/artifacts/R31_ORGAN_TRANSPORT.lean\n")

file(MAKE_DIRECTORY "${PROJECT_BINARY_DIR}/artifacts" "${PROJECT_BINARY_DIR}/receipts")
set(R31_CULTIVATION_DEED "${PROJECT_BINARY_DIR}/receipts/R31_ORGAN_CULTIVATION_DEED.txt")
set(R31_INTERMEDIATE_REST "${PROJECT_BINARY_DIR}/artifacts/R31_CULTIVATED_ORGANS.rest")
set(R31_CULTIVATION_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R31_CULTIVATED_ORGANS.lean")
set(R31_CULTIVATION_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R31_CULTIVATED_ORGANS.olean")
set(R31_CULTIVATION_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R31_CULTIVATION_STDOUT.txt")
set(R31_CULTIVATION_STDERR "${PROJECT_BINARY_DIR}/artifacts/R31_CULTIVATION_STDERR.txt")
set(R31_CULTIVATION_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R31_CULTIVATION_ATLAS.tsv")
set(R31_APPLICATION_DEED "${PROJECT_BINARY_DIR}/receipts/R31_CULTIVATED_APPLICATION_DEED.txt")
set(R31_FINAL_REST "${PROJECT_BINARY_DIR}/artifacts/R31_CULTIVATED_APPLICATION_HANDOFF.rest")
set(R31_APPLICATION_SOURCE "${PROJECT_BINARY_DIR}/artifacts/R31_ORGAN_TRANSPORT.lean")
set(R31_APPLICATION_OLEAN "${PROJECT_BINARY_DIR}/artifacts/R31_ORGAN_TRANSPORT.olean")
set(R31_APPLICATION_STDOUT "${PROJECT_BINARY_DIR}/artifacts/R31_APPLICATION_STDOUT.txt")
set(R31_APPLICATION_STDERR "${PROJECT_BINARY_DIR}/artifacts/R31_APPLICATION_STDERR.txt")
set(R31_DOSSIER "${PROJECT_BINARY_DIR}/artifacts/R31_CULTIVATED_ORGAN_DOSSIER.md")
set(R31_APPLICATION_ATLAS "${PROJECT_BINARY_DIR}/artifacts/R31_APPLICATION_ATLAS.tsv")
set(R31_CULTIVATION_OPEN_LOG "${PROJECT_BINARY_DIR}/artifacts/R31_CULTIVATION_OPEN_PATHS.txt")
set(R31_APPLICATION_OPEN_LOG "${PROJECT_BINARY_DIR}/artifacts/R31_APPLICATION_OPEN_PATHS.txt")
set(R31_SOURCE_AUDIT "${PROJECT_BINARY_DIR}/receipts/R31_SOURCE_ACCESS_AUDIT.txt")
set(R31_SEAL "${PROJECT_BINARY_DIR}/receipts/R31_SEALED_RETURN.txt")
set(R31_DETERMINISM "${PROJECT_BINARY_DIR}/receipts/R31_DETERMINISM.txt")

holonic_found(NAME r31.organ_cultivation_device_deed
  EXECUTABLE r31_organ_cultivation_device_deed
  COMMAND
    "${R31_CULTIVATION_DEED}" "${R30_FINAL_REST}" "${R31_INTERMEDIATE_REST}"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_R18_RECIPROCAL.card"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_R24_CENTRAL_WALK.card"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_R29_SIGNED_TRACE.card"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_R30_POLYGONS.card"
    "${R31_CULTIVATION_SOURCE}" "${R31_CULTIVATION_OLEAN}" "${R31_CULTIVATION_STDOUT}"
    "${R31_CULTIVATION_STDERR}" "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R31_CULTIVATION_ATLAS}")

holonic_found(NAME r31.cultivated_application_device_deed
  EXECUTABLE r31_cultivated_application_device_deed
  COMMAND
    "${R31_APPLICATION_DEED}" "${R31_INTERMEDIATE_REST}" "${R31_FINAL_REST}"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_CONDUCTANCE_STAR.card"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_SQUARE_WALK.card"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_SIGNED_CARRIER.card"
    "${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_GRADED_INCIDENCE.card"
    "${R31_APPLICATION_SOURCE}" "${R31_APPLICATION_OLEAN}" "${R31_APPLICATION_STDOUT}"
    "${R31_APPLICATION_STDERR}" "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${PROJECT_BINARY_DIR}/artifacts" "${R31_DOSSIER}" "${R31_APPLICATION_ATLAS}")

add_library(r31_open_probe SHARED tests/apparatus/r31_open_probe.cpp)
target_link_libraries(r31_open_probe PRIVATE holonics_contract_options)
set_target_properties(r31_open_probe PROPERTIES PREFIX "")
holonic_found(NAME r31.source_access_audit
  COMMAND
    "${CMAKE_COMMAND}" -DCULT_EXEC=$<TARGET_FILE:r31_organ_cultivation_device_deed>
    -DAPP_EXEC=$<TARGET_FILE:r31_cultivated_application_device_deed>
    -DPROBE=$<TARGET_FILE:r31_open_probe> -DCULT_LOG=${R31_CULTIVATION_OPEN_LOG}
    -DAPP_LOG=${R31_APPLICATION_OPEN_LOG} -DOUTPUT=${R31_SOURCE_AUDIT}
    -DCULT_DEED=${R31_CULTIVATION_DEED} -DAPP_DEED=${R31_APPLICATION_DEED}
    -DR30_REST=${R30_FINAL_REST} -DINTERMEDIATE=${R31_INTERMEDIATE_REST}
    -DFINAL_REST=${R31_FINAL_REST}
    -DD0=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_R18_RECIPROCAL.card
    -DD1=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_R24_CENTRAL_WALK.card
    -DD2=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_R29_SIGNED_TRACE.card
    -DD3=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_R30_POLYGONS.card
    -DH0=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_CONDUCTANCE_STAR.card
    -DH1=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_SQUARE_WALK.card
    -DH2=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_SIGNED_CARRIER.card
    -DH3=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_GRADED_INCIDENCE.card
    -DCULT_SOURCE=${R31_CULTIVATION_SOURCE} -DCULT_OLEAN=${R31_CULTIVATION_OLEAN}
    -DCULT_STDOUT=${R31_CULTIVATION_STDOUT} -DCULT_STDERR=${R31_CULTIVATION_STDERR}
    -DCULT_ATLAS=${R31_CULTIVATION_ATLAS} -DAPP_SOURCE=${R31_APPLICATION_SOURCE}
    -DAPP_OLEAN=${R31_APPLICATION_OLEAN} -DAPP_STDOUT=${R31_APPLICATION_STDOUT}
    -DAPP_STDERR=${R31_APPLICATION_STDERR} -DDOSSIER=${R31_DOSSIER}
    -DAPP_ATLAS=${R31_APPLICATION_ATLAS}
    -DFORMAL_ROOT=${PROJECT_SOURCE_DIR}/formal/elementary-holonics
    -DTOOLCHAIN=${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain
    -DMANIFEST=${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json
    -DARTIFACT_ROOT=${PROJECT_BINARY_DIR}/artifacts -P
    "${PROJECT_SOURCE_DIR}/cmake/R31SourceAccessAudit.cmake")
holonic_found(NAME r31.determinism
  WITHHOLD TMP
  COMMAND
    "${CMAKE_COMMAND}" -DCULT_EXEC=$<TARGET_FILE:r31_organ_cultivation_device_deed>
    -DAPP_EXEC=$<TARGET_FILE:r31_cultivated_application_device_deed>
    -DTMP=${PROJECT_BINARY_DIR}/artifacts/r31-determinism -DR30_REST=${R30_FINAL_REST}
    -DD0=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_R18_RECIPROCAL.card
    -DD1=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_R24_CENTRAL_WALK.card
    -DD2=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_R29_SIGNED_TRACE.card
    -DD3=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_R30_POLYGONS.card
    -DH0=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_CONDUCTANCE_STAR.card
    -DH1=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_SQUARE_WALK.card
    -DH2=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_SIGNED_CARRIER.card
    -DH3=${PROJECT_SOURCE_DIR}/src/apparatus/cards/R31_GRADED_INCIDENCE.card
    -DFORMAL_ROOT=${PROJECT_SOURCE_DIR}/formal/elementary-holonics
    -DTOOLCHAIN=${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain
    -DMANIFEST=${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json
    -DARTIFACT_ROOT=${PROJECT_BINARY_DIR}/artifacts -DCULT_DEED=${R31_CULTIVATION_DEED}
    -DAPP_DEED=${R31_APPLICATION_DEED} -DINTERMEDIATE=${R31_INTERMEDIATE_REST}
    -DFINAL_REST=${R31_FINAL_REST} -DCULT_SOURCE=${R31_CULTIVATION_SOURCE}
    -DCULT_OLEAN=${R31_CULTIVATION_OLEAN} -DCULT_STDOUT=${R31_CULTIVATION_STDOUT}
    -DCULT_STDERR=${R31_CULTIVATION_STDERR} -DCULT_ATLAS=${R31_CULTIVATION_ATLAS}
    -DAPP_SOURCE=${R31_APPLICATION_SOURCE} -DAPP_OLEAN=${R31_APPLICATION_OLEAN}
    -DAPP_STDOUT=${R31_APPLICATION_STDOUT} -DAPP_STDERR=${R31_APPLICATION_STDERR}
    -DDOSSIER=${R31_DOSSIER} -DAPP_ATLAS=${R31_APPLICATION_ATLAS}
    -DOUTPUT=${R31_DETERMINISM} -P "${PROJECT_SOURCE_DIR}/cmake/R31Determinism.cmake")
holonic_found(NAME r31.seal
  COMMAND
    "${CMAKE_COMMAND}" -DOUTPUT=${R31_SEAL} -DSOURCE_AUDIT=${R31_SOURCE_AUDIT}
    -DCULT_DEED=${R31_CULTIVATION_DEED} -DAPP_DEED=${R31_APPLICATION_DEED}
    -DINTERMEDIATE=${R31_INTERMEDIATE_REST} -DFINAL_REST=${R31_FINAL_REST}
    -DCULT_SOURCE=${R31_CULTIVATION_SOURCE} -DCULT_OLEAN=${R31_CULTIVATION_OLEAN}
    -DCULT_ATLAS=${R31_CULTIVATION_ATLAS} -DAPP_SOURCE=${R31_APPLICATION_SOURCE}
    -DAPP_OLEAN=${R31_APPLICATION_OLEAN} -DDOSSIER=${R31_DOSSIER}
    -DAPP_ATLAS=${R31_APPLICATION_ATLAS} -DDETERMINISM=${R31_DETERMINISM} -P
    "${PROJECT_SOURCE_DIR}/cmake/R31Seal.cmake")
holonic_found(NAME r31.cultivated_host_conformance
  EXECUTABLE r31_cultivated_host_conformance
  COMMAND
   )
add_test(NAME r31.forbidden_cultivated_copy COMMAND "${CMAKE_COMMAND}"
  -DCOMPILER=${CMAKE_CXX_COMPILER}
  -DSOURCE=${PROJECT_SOURCE_DIR}/tests/compile_contracts/forbidden_cultivated_copy.cpp
  -DINCLUDE_DIRECTORY=${PROJECT_SOURCE_DIR}/src/include
  "-DEXPECTED_TEXT=use of deleted function"
  -P "${PROJECT_SOURCE_DIR}/cmake/ExpectCompileFailure.cmake")

set(R31_EXTRA_ARTIFACTS
  "$<TARGET_FILE:r31_organ_cultivation_device_deed>|$<TARGET_FILE:r31_cultivated_application_device_deed>|${R31_DEVICE_PTX}|${R31_DEVICE_CUBIN}")
set(R31_DEVICE_PTX_LIST "${R31_DEVICE_PTX}")
set(R31_DEVICE_CUBIN_LIST "${R31_DEVICE_CUBIN}")
