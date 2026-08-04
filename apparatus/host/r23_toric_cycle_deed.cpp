#include <fstream>

#include <holonics/apparatus/toric_cycle_executor.hpp>
#include <holonics/apparatus/toric_cycle_probe.hpp>
#include <holonics/apparatus/toric_cycle_store_adapter.hpp>

#include "r23_artifact.hpp"
#include "r23_cases.hpp"
#include "r23_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 14) { return 2; }
  holonics::organ::toric_cycle_card card{};
  holonics::event::cm_incidence_rest_record inherited{};
  const auto card_load = holonics::apparatus::read_toric_cycle_card(argv[4], card);
  const auto rest_load = holonics::apparatus::read_cm_incidence_handoff(argv[2], inherited);
  if (!card_load.returned() || !rest_load.returned()) { return 3; }
  const auto mount = holonics::tests::r23_case(inherited, card);
  auto variation = mount.foundation;
  variation.card.targets[0].response[0].numerator = 4;
  variation.card.targets[0].response[2].numerator = 4;
  holonics::organ::toric_cycle_receipt changed{};
  const auto probe = holonics::apparatus::probe_toric_derivation(variation, changed);
  const holonics::apparatus::lean_process_configuration process{
      argv[9], argv[10], argv[11], argv[5], argv[6], argv[7], argv[8], argv[12]};
  holonics::event::toric_cycle_observation observation{};
  holonics::event::toric_cycle_rest_record handoff{};
  const auto execution =
      holonics::apparatus::execute_toric_cycle(mount, process, observation, handoff);
  const auto rest_write = holonics::apparatus::write_toric_cycle_handoff(argv[3], handoff);
  const auto failures = holonics::tests::r23_verification_failures(card_load, rest_load,
      execution, probe, changed, observation, handoff) + !rest_write.returned();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  std::ofstream atlas{argv[13], std::ios::binary | std::ios::trunc};
  if (!deed || !atlas) { return 4; }
  holonics::tests::write_r23_artifact(deed, card_load, rest_load, rest_write,
      execution, probe, changed, observation, handoff, failures);
  holonics::tests::write_r23_atlas(atlas, observation.inquiry);
  return failures == 0 ? 0 : 1;
}
