#include <fstream>

#include <holonics/apparatus/causal_linear_executor.hpp>
#include <holonics/apparatus/causal_linear_probe.hpp>
#include <holonics/apparatus/causal_linear_store_adapter.hpp>
#include <holonics/apparatus/cm_incidence_store_adapter.hpp>
#include <holonics/apparatus/toric_cycle_store_adapter.hpp>
#include <holonics/apparatus/algebraic_variation_store_adapter.hpp>

#include "r25_artifact.hpp"
#include "r25_cases.hpp"
#include "r25_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 17) { return 2; }
  holonics::organ::causal_linear_card card{};
  holonics::organ::cm_problem_card cm{}; holonics::organ::toric_cycle_card toric{};
  holonics::organ::algebraic_variation_card variation{};
  holonics::event::algebraic_variation_rest_record inherited{};
  const auto card_load = holonics::apparatus::read_causal_linear_card(argv[4], card);
  const auto cm_load = holonics::apparatus::read_cm_problem_card(argv[5], cm);
  const auto toric_load = holonics::apparatus::read_toric_cycle_card(argv[6], toric);
  const auto variation_load = holonics::apparatus::read_algebraic_variation_card(
      argv[7], variation);
  const auto rest_load = holonics::apparatus::read_algebraic_variation_handoff(
      argv[2], inherited);
  const bool sources_loaded = card_load.returned() && cm_load.returned() &&
      toric_load.returned() && variation_load.returned();
  if (!sources_loaded || !rest_load.returned()) { return 3; }
  const auto mount = holonics::tests::r25_case(inherited, card, cm, toric, variation);
  auto changed_foundation = mount.foundation; changed_foundation.card.phase_second = 4;
  holonics::organ::causal_linear_receipt changed{};
  const auto probe = holonics::apparatus::probe_causal_linear(changed_foundation, changed);
  const holonics::apparatus::lean_process_configuration process{
      argv[12], argv[13], argv[14], argv[8], argv[9], argv[10], argv[11], argv[15]};
  holonics::event::causal_linear_observation observation{};
  holonics::event::causal_linear_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_causal_linear(
      mount, process, observation, handoff);
  const auto rest_write = holonics::apparatus::write_causal_linear_handoff(argv[3], handoff);
  const auto failures = holonics::tests::r25_verification_failures(sources_loaded, rest_load,
      execution, probe, changed, observation, handoff) + !rest_write.returned();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  std::ofstream atlas{argv[16], std::ios::binary | std::ios::trunc};
  if (!deed || !atlas) { return 4; }
  holonics::tests::write_r25_artifact(deed, sources_loaded, card_load, rest_load, rest_write,
      execution, probe, changed, observation, handoff, failures);
  holonics::tests::write_r25_atlas(atlas, observation.inquiry);
  return failures == 0 ? 0 : 1;
}
