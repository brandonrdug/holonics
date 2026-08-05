#include <fstream>

#include <holonics/apparatus/algebraic_variation_store_adapter.hpp>
#include <holonics/apparatus/cm_incidence_store_adapter.hpp>
#include <holonics/apparatus/intrinsic_hypergeometry_executor.hpp>
#include <holonics/apparatus/intrinsic_hypergeometry_store_adapter.hpp>

#include "r26_artifact.hpp"
#include "r26_cases.hpp"
#include "r26_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 16) { return 2; }
  holonics::organ::intrinsic_hypergeometry_card card{};
  holonics::organ::cm_problem_card cm{};
  holonics::organ::algebraic_variation_card variation{};
  holonics::event::causal_linear_rest_record inherited{};
  const auto card_load = holonics::apparatus::read_intrinsic_hypergeometry_card(argv[4], card);
  const auto cm_load = holonics::apparatus::read_cm_problem_card(argv[5], cm);
  const auto variation_load = holonics::apparatus::read_algebraic_variation_card(
      argv[6], variation);
  const auto rest_load = holonics::apparatus::read_causal_linear_handoff(argv[2], inherited);
  const bool sources_loaded = card_load.returned() && cm_load.returned() &&
      variation_load.returned();
  if (!sources_loaded || !rest_load.returned()) { return 3; }
  const auto mount = holonics::tests::r26_case(inherited, card, cm, variation);
  const holonics::apparatus::lean_process_configuration process{
      argv[11], argv[12], argv[13], argv[7], argv[8], argv[9], argv[10], argv[14]};
  holonics::event::intrinsic_hypergeometry_observation observation{};
  holonics::event::intrinsic_hypergeometry_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_intrinsic_hypergeometry(
      mount, process, observation, handoff);
  const auto rest_write = holonics::apparatus::write_intrinsic_hypergeometry_handoff(
      argv[3], handoff);
  const auto failures = holonics::tests::r26_verification_failures(sources_loaded, rest_load,
      execution, observation, handoff) + !rest_write.returned();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  std::ofstream atlas{argv[15], std::ios::binary | std::ios::trunc};
  if (!deed || !atlas) { return 4; }
  holonics::tests::write_r26_artifact(deed, sources_loaded, card_load, rest_load, rest_write,
      execution, observation, handoff, failures);
  holonics::tests::write_r26_atlas(atlas, observation);
  return failures == 0 ? 0 : 1;
}
