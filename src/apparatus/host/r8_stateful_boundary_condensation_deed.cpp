#include <fstream>
#include <iostream>

#include <holonics/apparatus/boundary_condensation_executor.hpp>

#include "r8_artifact.hpp"
#include "r8_cases.hpp"
#include "r8_oracle.hpp"
#include "r8_verify.hpp"

int main(int argument_count, char** arguments) {
  if (argument_count != 2) {
    std::cerr << "expected one boundary-condensation artifact path\n";
    return 2;
  }
  const auto mount = holonics::tests::r8_case();
  holonics::apparatus::boundary_condensation_observation actual{};
  const auto execution = holonics::apparatus::execute_boundary_condensation(mount, actual);
  const auto oracle = holonics::tests::r8_oracle(mount);
  const std::size_t failures =
      holonics::tests::r8_verification_failures(execution, actual, oracle);
  std::ofstream artifact{arguments[1], std::ios::trunc};
  if (!artifact) {
    std::cerr << "could not open boundary-condensation artifact\n";
    return 3;
  }
  holonics::tests::write_r8_artifact(artifact, execution, actual, failures);
  artifact.flush();
  if (failures != 0) {
    std::cerr << "boundary-condensation return verification failed\n";
    return 4;
  }
  return 0;
}
