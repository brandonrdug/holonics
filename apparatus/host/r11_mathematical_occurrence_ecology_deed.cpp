#include <fstream>

#include <holonics/apparatus/mathematical_ecology_executor.hpp>
#include <holonics/apparatus/mathematical_source_adapter.hpp>

#include "r11_artifact.hpp"
#include "r11_cases.hpp"
#include "r11_oracle.hpp"
#include "r11_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 5) { return 2; }
  const char* paths[2]{argv[2], argv[3]};
  auto original = holonics::apparatus::mount_mathematical_sources(paths, 2, 73);
  auto relocated = holonics::apparatus::mount_relocated_mathematical_sources(
      paths, 2, 127, argv[4]);
  const bool exact_material = holonics::apparatus::same_mathematical_material(
      original.environment, relocated.environment);
  const auto original_receipt = original.receipt;
  const auto relocated_receipt = relocated.receipt;
  const auto mount = holonics::tests::r11_case(original_receipt.material_testimony);
  original.environment.detach();
  relocated.environment.detach();
  const bool sources_detached =
      !original.environment.admitted() && !relocated.environment.admitted();
  holonics::apparatus::mathematical_ecology_observation observation{};
  const auto execution = holonics::apparatus::execute_mathematical_ecology(mount, observation);
  const auto expected = holonics::tests::r11_oracle();
  const auto failures = holonics::tests::r11_verification_failures(execution, observation,
      original_receipt, relocated_receipt, exact_material, sources_detached, expected);
  std::ofstream output{argv[1], std::ios::binary | std::ios::trunc};
  if (!output) { return 3; }
  holonics::tests::write_r11_artifact(output, execution, observation,
      original_receipt, relocated_receipt, exact_material, sources_detached, failures);
  return failures == 0 ? 0 : 1;
}
