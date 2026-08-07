#include <fstream>
#include <iostream>

#include <holonics/apparatus/body_lifecycle_executor.hpp>

#include "r4_artifact.hpp"
#include "r4_verify.hpp"

int main(int argument_count, char** arguments) {
  if (argument_count != 2) {
    std::cerr << "expected one body lifecycle artifact path\n";
    return 2;
  }
  const auto input = holonics::tests::r4_input();
  holonics::event::lifecycle_output output{};
  const auto execution = holonics::apparatus::execute_body_lifecycle(input, output);
  const std::size_t failures = holonics::tests::r4_verification_failures(input, execution, output);
  std::ofstream artifact{arguments[1], std::ios::trunc};
  if (!artifact) {
    std::cerr << "could not open body lifecycle artifact\n";
    return 3;
  }
  holonics::tests::write_r4_artifact(artifact, execution, output, failures);
  artifact.flush();
  if (failures != 0) {
    std::cerr << "body lifecycle return verification failed\n";
    return 4;
  }
  return 0;
}
