# The grown circuit's invariant factors.
#
# Host-only and allocation-free: the reduction rebases a working set bounded by
# the incidence population, never by the product of the cell populations.

add_executable(grown_circuit_deed src/apparatus/host/grown_circuit_deed.cpp)
target_link_libraries(grown_circuit_deed
  PRIVATE holonics::structure holonics_contract_options)

set(GROWN_CIRCUIT_DEED "${PROJECT_BINARY_DIR}/receipts/GROWN_CIRCUIT_DEED.txt")
holonic_found(NAME grown_circuit.invariant_factors
  EXECUTABLE grown_circuit_deed
  COMMAND "${GROWN_CIRCUIT_DEED}")
