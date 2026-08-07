#include <cstddef>
#include <fstream>
#include <iostream>
#include <utility>

#include <holonics/apparatus/source_store_adapter.hpp>
#include <holonics/apparatus/source_topology_executor.hpp>

#include "r3_artifact.hpp"
#include "r3_verify.hpp"

int main(int argument_count, char** arguments) {
  constexpr std::size_t source_count = 3;
  if (argument_count != 6) {
    std::cerr << "expected artifact, three source paths, and relocation path\n";
    return 2;
  }
  const char* source_paths[source_count]{arguments[2], arguments[3], arguments[4]};
  auto original = holonics::apparatus::mount_source_store(source_paths, source_count);
  auto relocated = holonics::apparatus::mount_relocated_source_store(
      source_paths, source_count, arguments[5]);
  const auto original_receipt = original.receipt;
  const auto relocated_receipt = relocated.receipt;
  const std::size_t environment_failures = holonics::tests::r3_environment_failures(
      original.environment, relocated.environment, original.receipt, relocated.receipt);
  const auto expected = holonics::tests::r3_oracle(original.environment);
  relocated.environment.detach();
  holonics::apparatus::source_topology_output returned{};
  const auto execution = holonics::apparatus::execute_source_topology(
      std::move(original.environment), returned);
  const std::size_t verification_failures = holonics::tests::r3_verification_failures(
      expected, returned, execution) + environment_failures;
  std::ofstream artifact{arguments[1], std::ios::trunc};
  if (!artifact) {
    std::cerr << "could not open source topology artifact\n";
    return 3;
  }
  holonics::tests::write_r3_artifact(artifact, source_paths, source_count,
      original_receipt, relocated_receipt, environment_failures,
      execution, returned, verification_failures);
  artifact.flush();
  if (verification_failures != 0) {
    std::cerr << "source topology return verification failed\n";
    return 4;
  }
  return 0;
}
