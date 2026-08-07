#include <fstream>

#include <holonics/apparatus/blind_reconstruction_executor.hpp>
#include <holonics/apparatus/blind_reconstruction_probe.hpp>
#include <holonics/apparatus/blind_reconstruction_store_adapter.hpp>

#include "r21_artifact.hpp"
#include "r21_cases.hpp"
#include "r21_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 19) { return 2; }
  holonics::organ::binary_code_problem_card code{};
  holonics::organ::moment_problem_card moments{};
  holonics::event::regular_singular_rest_record inherited{};
  const auto code_load = holonics::apparatus::read_binary_code_card(argv[4], code);
  const auto moment_load = holonics::apparatus::read_moment_problem_card(argv[5], moments);
  const auto rest_load = holonics::apparatus::read_regular_singular_handoff(argv[2], inherited);
  if (!code_load.returned() || !moment_load.returned() || !rest_load.returned()) { return 3; }
  const auto mount = holonics::tests::r21_case(inherited, code, moments);
  auto code_variation = mount.foundation;
  code_variation.code.parity_rows[0] = 83;
  holonics::organ::blind_reconstruction_receipt changed_code{};
  const auto code_probe =
      holonics::apparatus::probe_blind_derivation(code_variation, changed_code);
  auto moment_variation = mount.foundation;
  const auto first_case = moment_variation.moments.cases[0];
  moment_variation.moments.cases[0] = moment_variation.moments.cases[1];
  moment_variation.moments.cases[1] = first_case;
  holonics::organ::blind_reconstruction_receipt changed_moment{};
  const auto moment_probe =
      holonics::apparatus::probe_blind_derivation(moment_variation, changed_moment);
  const holonics::apparatus::blind_checker_configuration process{
      {argv[14], argv[15], argv[16], argv[6], argv[7], argv[8], argv[9], argv[17]},
      {argv[14], argv[15], argv[16], argv[10], argv[11], argv[12], argv[13], argv[17]}};
  holonics::event::blind_reconstruction_observation observation{};
  holonics::event::blind_reconstruction_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_blind_reconstruction(
      mount, process, observation, handoff);
  const auto rest_write =
      holonics::apparatus::write_blind_reconstruction_handoff(argv[3], handoff);
  const auto failures = holonics::tests::r21_verification_failures(code_load, moment_load,
      rest_load, execution, code_probe, changed_code, moment_probe, changed_moment,
      observation, handoff) + !rest_write.returned();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  std::ofstream atlas{argv[18], std::ios::binary | std::ios::trunc};
  if (!deed || !atlas) { return 4; }
  holonics::tests::write_r21_artifact(deed, code_load, moment_load, rest_load, rest_write,
      execution, code_probe, moment_probe, observation, handoff, failures);
  holonics::tests::write_r21_atlas(atlas, observation.inquiry);
  return failures == 0 ? 0 : 1;
}
