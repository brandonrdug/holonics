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
  const auto ablation = holonics::tests::cultivation_ablation();
  if (!ablation.holds) {
    std::cerr << "PHASE 6 GRADE FAILED: mounted=" << ablation.mounted_only
              << " withheld=" << ablation.mounted_withheld
              << " cultivated=" << ablation.cultivated
              << " novel=" << ablation.novel_after_departure
              << " ablated_stops=" << ablation.ablated_stops_conducting << '\n';
    ++failures;
  } else {
    std::cerr << "phase 6 grade: mounted-only withheld 9*8; cultivated returned "
              << ablation.cultivated << "; source-detached returned "
              << ablation.novel_after_departure << " for novel 7*9; ablation stops conduct\n";
  }
  return failures == 0 ? 0 : 1;
}
