#include <array>
#include <cstddef>
#include <iostream>

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
  return failures == 0 ? 0 : 1;
}
