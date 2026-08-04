#include <fstream>

#include <holonics/apparatus/geometry_inquiry_executor.hpp>
#include <holonics/apparatus/geometry_inquiry_store_adapter.hpp>
#include <holonics/apparatus/sealed_geometry_reference_adapter.hpp>

#include "r17_artifact.hpp"
#include "r17_cases.hpp"
#include "r17_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 13) { return 2; }
  holonics::event::terminal_theorem_rest_record inherited{};
  const auto rest_load = holonics::apparatus::read_terminal_theorem_rest(argv[2], inherited);
  const auto mount = holonics::tests::r17_case(inherited);
  const holonics::apparatus::lean_process_configuration process{
      argv[8], argv[9], argv[10], argv[4], argv[5], argv[6], argv[7], argv[11]};
  holonics::event::geometry_inquiry_observation observation{};
  holonics::event::geometry_inquiry_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_geometry_inquiry(
      mount, process, observation, handoff);
  const auto comparison = holonics::apparatus::compare_sealed_geometry_reference(
      argv[12], execution.returned() && observation.typed.kernel_boundary_crossed);
  const auto rest_write = holonics::apparatus::write_geometry_inquiry_rest(argv[3], handoff);
  const auto failures = holonics::tests::r17_verification_failures(
      rest_load, execution, observation, handoff, comparison) + !rest_write.returned();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  if (!deed) { return 3; }
  holonics::tests::write_r17_artifact(
      deed, rest_load, rest_write, execution, observation, handoff, comparison, failures);
  return failures == 0 ? 0 : 1;
}
