#include <fstream>

#include <holonics/apparatus/lean_checker_executor.hpp>

#include "r13_artifact.hpp"
#include "r13_cases.hpp"
#include "r13_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 11) { return 2; }
  const auto mount = holonics::tests::r13_case(argv[2]);
  const holonics::apparatus::lean_process_configuration process{
      argv[7], argv[8], argv[9], argv[3], argv[4], argv[5], argv[6], argv[10]};
  holonics::event::checker_observation observation{};
  const auto execution = holonics::apparatus::execute_lean_checker(
      mount, process, observation);
  const auto failures = holonics::tests::r13_verification_failures(execution, observation);
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  if (!deed) { return 3; }
  holonics::tests::write_r13_artifact(deed, execution, observation, failures);
  return failures == 0 ? 0 : 1;
}
