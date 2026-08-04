#include <fstream>
#include <iostream>

#include <holonics/apparatus/conditioning_executor.hpp>

#include "r10_artifact.hpp"
#include "r10_cases.hpp"
#include "r10_oracle.hpp"
#include "r10_verify.hpp"

int main(int argument_count, char** arguments) {
  if (argument_count != 2) {
    std::cerr << "expected one conditioning artifact path\n"; return 2;
  }
  const auto mount = holonics::tests::r10_case();
  holonics::apparatus::conditioning_observation actual{};
  const auto execution = holonics::apparatus::execute_conditioning(mount, actual);
  const std::size_t failures = holonics::tests::r10_verification_failures(
      execution, actual, holonics::tests::r10_oracle());
  std::ofstream artifact{arguments[1], std::ios::trunc};
  if (!artifact) { std::cerr << "could not open conditioning artifact\n"; return 3; }
  holonics::tests::write_r10_artifact(artifact, execution, actual, failures);
  artifact.flush();
  if (failures != 0) {
    std::cerr << "conditioning return verification failed\n"; return 4;
  }
  return 0;
}
