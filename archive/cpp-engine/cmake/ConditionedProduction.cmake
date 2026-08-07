add_executable(
  conditioned_production_deed
  src/apparatus/host/conditioned_production_deed.cpp
  src/apparatus/host/lean_checker_process.cpp)
target_include_directories(
  conditioned_production_deed PRIVATE "${PROJECT_SOURCE_DIR}/src/apparatus/host")
target_link_libraries(
  conditioned_production_deed PRIVATE holonics::apparatus holonics_contract_options)

set(CONDITIONED_ARTIFACTS "${PROJECT_BINARY_DIR}/artifacts")
set(CONDITIONED_DEED_ARTIFACT
    "${PROJECT_BINARY_DIR}/receipts/CONDITIONED_PRODUCTION_DEED.txt")
# The foil is a proof the kernel is SUPPOSED to refuse, so no object is ever
# produced at this path. Its absence is the negative control and must not be read
# as work left undone by any founding that names it.
holonic_withhold("${CONDITIONED_ARTIFACTS}/HolonicsConditionedFoil.olean")

holonic_found(NAME conditioned.production_deed
  EXECUTABLE conditioned_production_deed
  COMMAND
    "${CONDITIONED_DEED_ARTIFACT}" "${CONDITIONED_ARTIFACTS}/HolonicsConditionedOne.lean"
    "${CONDITIONED_ARTIFACTS}/HolonicsConditionedTwo.lean"
    "${CONDITIONED_ARTIFACTS}/HolonicsConditionedFoil.lean"
    "${CONDITIONED_ARTIFACTS}/HolonicsConditionedOne.olean"
    "${CONDITIONED_ARTIFACTS}/HolonicsConditionedTwo.olean"
    "${CONDITIONED_ARTIFACTS}/HolonicsConditionedFoil.olean"
    "${CONDITIONED_ARTIFACTS}/CONDITIONED_STDOUT.txt"
    "${CONDITIONED_ARTIFACTS}/CONDITIONED_STDERR.txt"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lean-toolchain"
    "${PROJECT_SOURCE_DIR}/formal/elementary-holonics/lake-manifest.json"
    "${CONDITIONED_ARTIFACTS}")
