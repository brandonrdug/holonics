#include <fstream>

#include <holonics/apparatus/terminal_bundle_store_adapter.hpp>
#include <holonics/apparatus/terminal_theorem_executor.hpp>
#include <holonics/apparatus/theorem_rest_store_adapter.hpp>

#include "r16_artifact.hpp"
#include "r16_cases.hpp"
#include "r16_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 15) { return 2; }
  holonics::event::theorem_production_rest_record inherited{};
  const auto rest_load = holonics::apparatus::read_theorem_production_rest(argv[2], inherited);
  holonics::event::dependent_theorem_setup setup{};
  const auto setup_load = holonics::apparatus::read_dependent_theorem_setup(argv[3], setup);
  const auto mount = holonics::tests::r16_case(inherited, setup);
  const holonics::apparatus::lean_process_configuration process{
      argv[11], argv[12], argv[13], argv[7], argv[8], argv[9], argv[10], argv[14]};
  holonics::event::terminal_theorem_observation observation{};
  holonics::event::terminal_theorem_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_terminal_theorem(
      mount, process, observation, handoff);
  holonics::apparatus::first_return_artifact_testimony first{};
  const auto first_collection = holonics::apparatus::collect_first_return_artifacts(
      argv[4], argv[5], first);
  const auto failures = holonics::tests::r16_verification_failures(rest_load, setup_load,
      first_collection, first, execution, observation, handoff);
  std::ofstream rest_output{argv[6], std::ios::binary | std::ios::trunc};
  if (!rest_output) { return 3; }
  rest_output.write(reinterpret_cast<const char*>(&handoff),
      static_cast<std::streamsize>(sizeof(handoff)));
  if (!rest_output) { return 4; }
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  if (!deed) { return 5; }
  holonics::tests::write_r16_artifact(
      deed, rest_load, setup_load, first, execution, observation, handoff, failures);
  return failures == 0 ? 0 : 1;
}
