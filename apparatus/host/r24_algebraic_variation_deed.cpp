#include <fstream>

#include <holonics/apparatus/algebraic_variation_executor.hpp>
#include <holonics/apparatus/algebraic_variation_probe.hpp>
#include <holonics/apparatus/algebraic_variation_store_adapter.hpp>

#include "r24_artifact.hpp"
#include "r24_cases.hpp"
#include "r24_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 14) { return 2; }
  holonics::organ::algebraic_variation_card card{};
  holonics::event::toric_cycle_rest_record inherited{};
  const auto card_load = holonics::apparatus::read_algebraic_variation_card(argv[4], card);
  const auto rest_load = holonics::apparatus::read_toric_cycle_handoff(argv[2], inherited);
  if (!card_load.returned() || !rest_load.returned()) { return 3; }
  const auto mount = holonics::tests::r24_case(inherited, card);
  auto variation = mount.foundation; variation.card.coefficients[1].parameter = 2;
  holonics::organ::algebraic_variation_receipt changed{};
  const auto probe = holonics::apparatus::probe_algebraic_variation(variation, changed);
  const holonics::apparatus::lean_process_configuration process{
      argv[9], argv[10], argv[11], argv[5], argv[6], argv[7], argv[8], argv[12]};
  holonics::event::algebraic_variation_observation observation{};
  holonics::event::algebraic_variation_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_algebraic_variation(
      mount, process, observation, handoff);
  const auto rest_write = holonics::apparatus::write_algebraic_variation_handoff(
      argv[3], handoff);
  const auto failures = holonics::tests::r24_verification_failures(card_load, rest_load,
      execution, probe, changed, observation, handoff) + !rest_write.returned();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  std::ofstream atlas{argv[13], std::ios::binary | std::ios::trunc};
  if (!deed || !atlas) { return 4; }
  holonics::tests::write_r24_artifact(deed, card_load, rest_load, rest_write,
      execution, probe, changed, observation, handoff, failures);
  holonics::tests::write_r24_atlas(atlas, observation.inquiry);
  return failures == 0 ? 0 : 1;
}
