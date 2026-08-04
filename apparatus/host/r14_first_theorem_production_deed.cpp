#include <fstream>

#include <holonics/apparatus/theorem_production_executor.hpp>

#include "r14_artifact.hpp"
#include "r14_cases.hpp"
#include "r14_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 11) { return 2; }
  const auto mount = holonics::tests::r14_case();
  const holonics::apparatus::lean_process_configuration process{
      argv[7], argv[8], argv[9], argv[3], argv[4], argv[5], argv[6], argv[10]};
  holonics::event::theorem_production_observation observation{};
  holonics::event::theorem_production_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_theorem_production(
      mount, process, observation, handoff);
  const auto failures = holonics::tests::r14_verification_failures(
      execution, observation, handoff);
  std::ofstream rest_output{argv[2], std::ios::binary | std::ios::trunc};
  if (!rest_output) { return 3; }
  rest_output.write(reinterpret_cast<const char*>(&handoff),
      static_cast<std::streamsize>(sizeof(handoff)));
  if (!rest_output) { return 4; }
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  if (!deed) { return 5; }
  holonics::tests::write_r14_artifact(deed, execution, observation, handoff, failures);
  return failures == 0 ? 0 : 1;
}
