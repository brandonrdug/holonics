#include <array>
#include <cstddef>
#include <iostream>

#include "ecology_cases.hpp"
#include "spine_cases.hpp"

int main() {
  const auto inputs = holonics::tests::spine_cases();
  const auto names = holonics::tests::spine_case_names();
  std::array<holonics::exact::spine_deed_output, holonics::tests::spine_case_count> outputs{};
  for (std::size_t slot = 0; slot < inputs.size(); ++slot) {
    outputs[slot] = holonics::body::execute_spine_deed(inputs[slot]);
    const auto repeated = holonics::body::execute_spine_deed(inputs[slot]);
    if (!holonics::exact::spine_deed_law::equal(outputs[slot], repeated)) {
      std::cerr << "spine deed was not deterministic at " << names[slot] << '\n';
      return 1;
    }
  }
  std::size_t failures = 0;
  if (!holonics::tests::swing_laws_hold(outputs)) {
    std::cerr << "swing laws failed\n"; ++failures;
  }
  if (!holonics::tests::standing_shares_rather_than_copies(outputs)) {
    std::cerr << "standing copied instead of sharing\n"; ++failures;
  }
  if (!holonics::tests::open_never_concludes(outputs)) {
    std::cerr << "an OPEN concluded or dropped its pair\n"; ++failures;
  }
  if (!holonics::tests::carrier_laws_hold()) {
    std::cerr << "minimum carrier laws failed\n"; ++failures;
  }
  if (!holonics::tests::substrate_laws_hold()) {
    std::cerr << "substrate laws failed\n"; ++failures;
  }
  if (!holonics::tests::information_laws_hold()) {
    std::cerr << "causal-information laws failed\n"; ++failures;
  }
  if (!holonics::tests::resonance_laws_hold()) {
    std::cerr << "resonance ecology laws failed\n"; ++failures;
  }
  if (!holonics::tests::suffix_laws_hold()) {
    std::cerr << "suffix ecology laws failed\n"; ++failures;
  }
  if (!holonics::tests::training_laws_hold()) {
    std::cerr << "training ecology laws failed\n"; ++failures;
  }
  if (!holonics::tests::reflective_laws_hold()) {
    std::cerr << "reflective runtime laws failed\n"; ++failures;
  }
  if (!holonics::tests::surface_laws_hold()) {
    std::cerr << "surface scale laws failed\n"; ++failures;
  }
  if (!holonics::tests::relational_laws_hold()) {
    std::cerr << "relational conduct laws failed\n"; ++failures;
  }
  if (!holonics::tests::mouth_laws_hold()) {
    std::cerr << "agentic mouth laws failed\n"; ++failures;
  }
  if (!holonics::tests::formal_laws_hold()) {
    std::cerr << "formal production laws failed\n"; ++failures;
  }
  if (!holonics::tests::research_laws_hold()) {
    std::cerr << "research ecology laws failed\n"; ++failures;
  }
  // The Phase 6 cultivation grade was withdrawn 2026-08-06 (CUT 5): the "founded
  // law" was the C++ multiply operator and the two developmental passages were one
  // constant twice.
  const auto cost = holonics::tests::suffix_cost_law();
  std::cerr << "phase 7 movement 1 cost law: symbols " << cost.small_symbols << " -> "
            << cost.large_symbols << "; states " << cost.small_states << " -> "
            << cost.large_states << "; formation " << cost.small_formation << " -> "
            << cost.large_formation << "; lookup " << cost.small_lookup << " -> "
            << cost.large_lookup << '\n';
  if (!cost.holds) {
    std::cerr << "PHASE 7 MOVEMENT 1 COST LAW FAILED: formation_linear="
              << cost.formation_linear << " lookup_linear=" << cost.lookup_linear << '\n';
    ++failures;
  }
  return failures == 0 ? 0 : 1;
}
