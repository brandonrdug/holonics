#include <cstddef>

#include <holonics/structure/structure_deed.hpp>

#include "r2_cases.hpp"
#include "r2_verify.hpp"

int main() {
  const auto inputs = holonics::tests::r2_cases();
  holonics::tests::r2_output_batch outputs{};
  for (std::size_t slot = 0; slot < inputs.size(); ++slot) {
    holonics::structure::resident_complex complex{inputs[slot].owner_seed};
    holonics::structure::admit_structure_case(complex, inputs[slot], outputs[slot]);
    holonics::structure::continue_structure_case(complex, inputs[slot], outputs[slot]);
  }
  return holonics::tests::r2_verification_failures(inputs, outputs) == 0 ? 0 : 1;
}
