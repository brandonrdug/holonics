#include <fstream>
#include <iostream>

#include <holonics/apparatus/weave_executor.hpp>

#include "r6_artifact.hpp"
#include "r6_cases.hpp"
#include "r6_oracle.hpp"
#include "r6_verify.hpp"

int main(int argument_count, char** arguments) {
  if (argument_count != 2) {
    std::cerr << "expected one many-current weave artifact path\n";
    return 2;
  }
  const auto mount = holonics::tests::r6_cases();
  holonics::apparatus::weave_batch_observation actual{};
  const auto execution = holonics::apparatus::execute_weave(mount, actual);
  const auto oracle = holonics::tests::r6_oracle(mount);
  const std::size_t failures =
      holonics::tests::r6_verification_failures(mount, execution, actual, oracle);
  std::ofstream artifact{arguments[1], std::ios::trunc};
  if (!artifact) {
    std::cerr << "could not open many-current weave artifact\n";
    return 3;
  }
  holonics::tests::write_r6_artifact(artifact, execution, actual, failures);
  artifact.flush();
  if (failures != 0) {
    std::cerr << "many-current weave return verification failed\n";
    return 4;
  }
  return 0;
}
