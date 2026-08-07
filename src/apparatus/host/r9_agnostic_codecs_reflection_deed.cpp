#include <fstream>
#include <iostream>

#include <holonics/apparatus/codec_store_adapter.hpp>
#include <holonics/apparatus/reflective_codec_executor.hpp>

#include "r9_artifact.hpp"
#include "r9_cases.hpp"
#include "r9_oracle.hpp"
#include "r9_verify.hpp"

int main(int argument_count, char** arguments) {
  if (argument_count != 4) {
    std::cerr << "expected artifact, codec source, and relocation paths\n";
    return 2;
  }
  auto original = holonics::apparatus::mount_codec_store(arguments[2]);
  auto relocated = holonics::apparatus::mount_relocated_codec_store(arguments[2], arguments[3]);
  if (original.receipt.state != holonics::apparatus::codec_store_status::exact ||
      relocated.receipt.state != holonics::apparatus::codec_store_status::exact ||
      !holonics::apparatus::same_codec_material(original.environment, relocated.environment)) {
    std::cerr << "codec source admission failed\n";
    return 3;
  }
  const auto mount = holonics::tests::r9_case(
      original.environment.value(), original.receipt, relocated.receipt);
  original.environment.detach();
  relocated.environment.detach();
  if (original.environment.admitted() || relocated.environment.admitted()) { return 4; }
  holonics::apparatus::reflective_codec_observation actual{};
  const auto execution = holonics::apparatus::execute_reflective_codec(mount, actual);
  const std::size_t failures = holonics::tests::r9_verification_failures(
      execution, actual, holonics::tests::r9_oracle());
  std::ofstream artifact{arguments[1], std::ios::trunc};
  if (!artifact) {
    std::cerr << "could not open codec-reflection artifact\n";
    return 5;
  }
  holonics::tests::write_r9_artifact(artifact, execution, actual, failures);
  artifact.flush();
  if (failures != 0) {
    std::cerr << "codec-reflection return verification failed\n";
    return 6;
  }
  return 0;
}
