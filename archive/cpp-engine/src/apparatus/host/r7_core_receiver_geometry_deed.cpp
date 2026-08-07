#include <fstream>
#include <iostream>

#include <holonics/apparatus/receiver_geometry_executor.hpp>

#include "r7_artifact.hpp"
#include "r7_cases.hpp"
#include "r7_oracle.hpp"
#include "r7_verify.hpp"

int main(int argument_count, char** arguments) {
  if (argument_count != 2) {
    std::cerr << "expected one receiver-geometry artifact path\n";
    return 2;
  }
  const auto mount = holonics::tests::r7_case();
  holonics::apparatus::receiver_geometry_observation actual{};
  const auto execution = holonics::apparatus::execute_receiver_geometry(mount, actual);
  const auto oracle = holonics::tests::r7_oracle(mount);
  const std::size_t failures =
      holonics::tests::r7_verification_failures(execution, actual, oracle);
  std::ofstream artifact{arguments[1], std::ios::trunc};
  if (!artifact) {
    std::cerr << "could not open receiver-geometry artifact\n";
    return 3;
  }
  holonics::tests::write_r7_artifact(artifact, execution, actual, failures);
  artifact.flush();
  if (failures != 0) {
    std::cerr << "receiver-geometry return verification failed\n";
    return 4;
  }
  return 0;
}
