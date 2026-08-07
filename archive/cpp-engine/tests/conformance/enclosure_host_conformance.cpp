#include <array>
#include <cstddef>
#include <iostream>

#include "enclosure_cases.hpp"

int main() {
  const auto inputs = holonics::tests::enclosure_cases();
  const auto names = holonics::tests::enclosure_case_names();
  std::array<holonics::exact::enclosure_deed_output, holonics::tests::enclosure_case_count>
      outputs{};

  std::size_t oracle_failures = 0;
  for (std::size_t slot = 0; slot < inputs.size(); ++slot) {
    outputs[slot] = holonics::exact::execute_enclosure_deed(inputs[slot]);
    if (!holonics::tests::independent_enclosure_agrees(inputs[slot], outputs[slot])) {
      std::cerr << "independent oracle refused case " << names[slot] << '\n';
      ++oracle_failures;
    }
  }

  const bool named = holonics::tests::certified_enclosure_returns(outputs);
  const bool ablation = holonics::tests::certificate_ablation_holds(outputs);
  const bool aperture = holonics::tests::aperture_refusal_holds(outputs);

  // Determinism: the same occurrence returns the same artifact.
  bool deterministic = true;
  for (std::size_t slot = 0; slot < inputs.size(); ++slot) {
    const auto repeated = holonics::exact::execute_enclosure_deed(inputs[slot]);
    if (!holonics::exact::enclosure_deed_law::equal(repeated, outputs[slot])) {
      deterministic = false;
    }
  }

  if (!named) {
    std::cerr << "named certified-enclosure returns failed\n";
  }
  if (!ablation) {
    std::cerr << "certificate ablation failed: the organ committed without its certificate\n";
  }
  if (!aperture) {
    std::cerr << "aperture refusal failed\n";
  }
  if (!deterministic) {
    std::cerr << "enclosure deed was not deterministic\n";
  }
  if (oracle_failures != 0 || !named || !ablation || !aperture || !deterministic) {
    return 1;
  }
  return 0;
}
