#include <fstream>

#include <holonics/apparatus/cm_incidence_executor.hpp>
#include <holonics/apparatus/cm_incidence_probe.hpp>
#include <holonics/apparatus/cm_incidence_store_adapter.hpp>

#include "r22_artifact.hpp"
#include "r22_cases.hpp"
#include "r22_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 14) { return 2; }
  holonics::organ::cm_problem_card card{};
  holonics::event::blind_reconstruction_rest_record inherited{};
  const auto card_load = holonics::apparatus::read_cm_problem_card(argv[4], card);
  const auto rest_load =
      holonics::apparatus::read_blind_reconstruction_handoff(argv[2], inherited);
  if (!card_load.returned() || !rest_load.returned()) { return 3; }
  const auto mount = holonics::tests::r22_case(inherited, card);
  auto variation = mount.foundation;
  variation.card.translation_count = 4;
  holonics::organ::cm_incidence_receipt changed{};
  const auto probe = holonics::apparatus::probe_cm_derivation(variation, changed);
  const holonics::apparatus::lean_process_configuration process{
      argv[9], argv[10], argv[11], argv[5], argv[6], argv[7], argv[8], argv[12]};
  holonics::event::cm_incidence_observation observation{};
  holonics::event::cm_incidence_rest_record handoff{};
  const auto execution =
      holonics::apparatus::execute_cm_incidence(mount, process, observation, handoff);
  const auto rest_write =
      holonics::apparatus::write_cm_incidence_handoff(argv[3], handoff);
  const auto failures = holonics::tests::r22_verification_failures(card_load, rest_load,
      execution, probe, changed, observation, handoff) + !rest_write.returned();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  std::ofstream atlas{argv[13], std::ios::binary | std::ios::trunc};
  if (!deed || !atlas) { return 4; }
  holonics::tests::write_r22_artifact(deed, card_load, rest_load, rest_write,
      execution, probe, changed, observation, handoff, failures);
  holonics::tests::write_r22_atlas(atlas, observation.inquiry);
  return failures == 0 ? 0 : 1;
}
