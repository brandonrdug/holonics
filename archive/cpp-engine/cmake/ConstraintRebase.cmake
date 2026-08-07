add_executable(constraint_rebase_deed src/apparatus/host/constraint_rebase_deed.cpp)
target_link_libraries(
  constraint_rebase_deed PRIVATE holonics::apparatus holonics_contract_options)

set(CONSTRAINT_DEED_ARTIFACT
    "${PROJECT_BINARY_DIR}/receipts/CONSTRAINT_REBASE_DEED.txt")
holonic_found(NAME constraint.rebase_deed
  EXECUTABLE constraint_rebase_deed
  COMMAND
    "${CONSTRAINT_DEED_ARTIFACT}")
