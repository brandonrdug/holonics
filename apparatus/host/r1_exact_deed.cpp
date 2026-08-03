#include <array>
#include <cstddef>
#include <fstream>
#include <iostream>

#include <holonics/apparatus/exact_executor.hpp>

#include "r1_artifact.hpp"
#include "r1_cases.hpp"
#include "r1_oracle.hpp"

int main(int argument_count, char** arguments) {
  if (argument_count != 2) {
    std::cerr << "expected one exact-deed artifact path\n";
    return 2;
  }

  const auto inputs = holonics::tests::r1_cases();
  std::array<holonics::exact::deed_output, holonics::tests::r1_case_count> device_outputs{};
  std::array<holonics::exact::deed_output, holonics::tests::r1_case_count> oracle_outputs{};

  const auto execution = holonics::apparatus::execute_exact_deeds(
      holonics::apparatus::exact_deed_batch{
          inputs.data(), device_outputs.data(), inputs.size()});
  if (!execution.returned()) {
    std::cerr << "device executor returned obstruction "
              << static_cast<unsigned>(execution.state) << '\n';
    return 3;
  }

  std::size_t parity_failures = 0;
  std::size_t exact_returns = 0;
  for (std::size_t slot = 0; slot < inputs.size(); ++slot) {
    oracle_outputs[slot] = holonics::tests::r1_oracle(inputs[slot]);
    if (!holonics::tests::equal_deed_output(device_outputs[slot], oracle_outputs[slot])) {
      ++parity_failures;
    }
    if (device_outputs[slot].state == holonics::exact::status::exact) {
      ++exact_returns;
    }
  }
  const std::size_t algebraic_failures =
      holonics::tests::r1_algebraic_failures(inputs, device_outputs);

  std::ofstream artifact{arguments[1], std::ios::trunc};
  if (!artifact) {
    std::cerr << "could not open exact-deed artifact\n";
    return 4;
  }
  holonics::tests::write_r1_artifact(
      artifact, execution, device_outputs, parity_failures, algebraic_failures, exact_returns);
  artifact.flush();

  if (parity_failures != 0 || algebraic_failures != 0 ||
      !holonics::tests::r1_named_returns_hold(device_outputs)) {
    std::cerr << "exact-deed parity or named return failed\n";
    return 5;
  }
  return 0;
}
