#include <fstream>
#include <iostream>

#include <holonics/apparatus/causal_current_executor.hpp>

#include "r5_artifact.hpp"
#include "r5_cases.hpp"
#include "r5_oracle.hpp"
#include "r5_verify.hpp"

int main(int argument_count, char** arguments) {
  if (argument_count != 2) {
    std::cerr << "expected one causal-current artifact path\n";
    return 2;
  }
  const auto mount = holonics::tests::r5_cases();
  holonics::current::current_batch_observation actual{};
  const auto execution = holonics::apparatus::execute_causal_current(mount, actual, 8, 9);
  const auto oracle = holonics::tests::r5_oracle(mount);
  holonics::current::current_batch_observation unavailable_output{};
  const auto unavailable =
      holonics::apparatus::execute_causal_current(mount, unavailable_output, 9, 0);
  const std::size_t failures = holonics::tests::r5_verification_failures(
      mount, execution, actual, oracle, unavailable);
  std::ofstream artifact{arguments[1], std::ios::trunc};
  if (!artifact) {
    std::cerr << "could not open causal-current artifact\n";
    return 3;
  }
  holonics::tests::write_r5_artifact(artifact, execution, actual, unavailable, failures);
  artifact.flush();
  if (failures != 0) {
    std::cerr << "causal-current return verification failed\n";
    return 4;
  }
  return 0;
}
