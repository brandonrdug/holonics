#include <fstream>

#include <holonics/apparatus/phase_crystal_executor.hpp>
#include <holonics/apparatus/phase_crystal_store_adapter.hpp>

#include "r18_artifact.hpp"
#include "r18_cases.hpp"
#include "r18_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 13) { return 2; }
  holonics::event::geometry_inquiry_rest_record inherited{};
  const auto rest_load = holonics::apparatus::read_geometry_inquiry_rest(argv[2], inherited);
  const auto mount = holonics::tests::r18_case(inherited);
  const holonics::apparatus::lean_process_configuration process{
      argv[8], argv[9], argv[10], argv[4], argv[5], argv[6], argv[7], argv[11]};
  holonics::event::phase_crystal_observation observation{};
  holonics::event::phase_crystal_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_phase_crystal(
      mount, process, observation, handoff);
  const auto rest_write = holonics::apparatus::write_phase_crystal_rest(argv[3], handoff);
  const auto failures = holonics::tests::r18_verification_failures(
      rest_load, execution, observation, handoff) + !rest_write.returned();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  std::ofstream atlas{argv[12], std::ios::binary | std::ios::trunc};
  if (!deed || !atlas) { return 3; }
  holonics::tests::write_r18_artifact(
      deed, rest_load, rest_write, execution, observation, handoff, failures);
  holonics::tests::write_r18_atlas(atlas, observation.inquiry);
  return failures == 0 ? 0 : 1;
}
