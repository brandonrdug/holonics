#include <array>
#include <cstddef>

#include <holonics/exact/deed_execute.hpp>

#include "r1_cases.hpp"
#include "r1_oracle.hpp"

int main() {
  const auto inputs = holonics::tests::r1_cases();
  std::array<holonics::exact::deed_output, holonics::tests::r1_case_count> outputs{};
  for (std::size_t slot = 0; slot < inputs.size(); ++slot) {
    outputs[slot] = holonics::exact::execute_deed(inputs[slot]);
    if (!holonics::tests::equal_deed_output(
            outputs[slot], holonics::tests::r1_oracle(inputs[slot]))) {
      return 1;
    }
  }
  if (!holonics::tests::r1_named_returns_hold(outputs) ||
      holonics::tests::r1_algebraic_failures(inputs, outputs) != 0) {
    return 2;
  }
  return 0;
}
