#include <fstream>
#include <iostream>

#include <holonics/apparatus/return_conditioning_executor.hpp>
#include <holonics/apparatus/theorem_rest_store_adapter.hpp>

#include "r15_artifact.hpp"
#include "r15_cases.hpp"
#include "r15_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 5) { return 2; }
  holonics::event::theorem_production_rest_record inherited{};
  const auto load = holonics::apparatus::read_theorem_production_rest(argv[2], inherited);
  const auto mount = holonics::tests::r15_case(inherited);
  holonics::event::return_conditioning_observation observation{};
  holonics::event::theorem_production_rest_record handoff{};
  holonics::event::dependent_theorem_setup setup{};
  const auto execution = holonics::apparatus::execute_return_conditioning(
      mount, observation, handoff, setup);
  const auto failures = holonics::tests::r15_verification_failures(
      load, mount, execution, observation, handoff, setup);
  std::ofstream handoff_output{argv[3], std::ios::binary | std::ios::trunc};
  if (!handoff_output) { return 3; }
  handoff_output.write(reinterpret_cast<const char*>(&handoff),
      static_cast<std::streamsize>(sizeof(handoff)));
  if (!handoff_output) { return 4; }
  std::ofstream setup_output{argv[4], std::ios::binary | std::ios::trunc};
  if (!setup_output) { return 5; }
  setup_output.write(reinterpret_cast<const char*>(&setup),
      static_cast<std::streamsize>(sizeof(setup)));
  if (!setup_output) { return 6; }
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  if (!deed) { return 7; }
  holonics::tests::write_r15_artifact(
      deed, load, execution, observation, handoff, setup, failures);
  return failures == 0 ? 0 : 1;
}
