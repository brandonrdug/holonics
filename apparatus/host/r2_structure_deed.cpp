#include <fstream>
#include <iostream>

#include <holonics/apparatus/structure_executor.hpp>

#include "r2_artifact.hpp"
#include "r2_cases.hpp"
#include "r2_verify.hpp"

int main(int argument_count, char** arguments) {
  if (argument_count != 2) {
    std::cerr << "expected one structure artifact path\n";
    return 2;
  }
  const auto inputs = holonics::tests::r2_cases();
  holonics::tests::r2_output_batch outputs{};
  const auto execution = holonics::apparatus::execute_structure_deeds(
      holonics::apparatus::structure_batch{inputs.data(), outputs.data(), inputs.size()});
  if (!execution.returned()) {
    std::cerr << "structure executor returned obstruction "
              << static_cast<unsigned>(execution.state) << '\n';
    return 3;
  }
  const std::size_t failures = holonics::tests::r2_verification_failures(inputs, outputs);
  std::ofstream artifact{arguments[1], std::ios::trunc};
  if (!artifact) {
    std::cerr << "could not open structure artifact\n";
    return 4;
  }
  holonics::tests::write_r2_artifact(artifact, execution, outputs, failures);
  artifact.flush();
  if (failures != 0) {
    std::cerr << "structure return verification failed\n";
    return 5;
  }
  return 0;
}
