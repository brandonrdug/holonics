#include <fstream>

#include <holonics/apparatus/hodge_realization_executor.hpp>
#include <holonics/apparatus/hodge_realization_store_adapter.hpp>
#include <holonics/event/expression_geometry_rest.hpp>

#include "r28_artifact.hpp"
#include "r28_atlas.hpp"
#include "r28_cases.hpp"
#include "r28_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 14) { return 2; }
  holonics::organ::hodge_realization_card card{};
  holonics::event::expression_geometry_rest_record inherited{};
  const auto card_load = holonics::apparatus::read_hodge_realization_card(argv[4], card);
  const auto rest_load = holonics::apparatus::read_expression_geometry_handoff(argv[2], inherited);
  const bool source_loaded = card_load.returned();
  if (!source_loaded || !rest_load.returned()) { return 3; }
  const auto mount = holonics::tests::r28_case(inherited, card);
  const holonics::apparatus::lean_process_configuration process{
      argv[9], argv[10], argv[11], argv[5], argv[6], argv[7], argv[8], argv[12]};
  holonics::event::hodge_realization_observation observation{};
  holonics::event::hodge_realization_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_hodge_realization(
      mount, process, observation, handoff);
  const auto rest_write = holonics::apparatus::write_hodge_realization_handoff(argv[3], handoff);
  const auto failures = holonics::tests::r28_verification_failures(source_loaded, rest_load,
      execution, observation, handoff) + !rest_write.returned();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  std::ofstream atlas{argv[13], std::ios::binary | std::ios::trunc};
  if (!deed || !atlas) { return 4; }
  holonics::tests::write_r28_artifact(deed, source_loaded, card_load, rest_load, rest_write,
      execution, observation, handoff, failures);
  holonics::tests::write_r28_atlas(atlas, observation);
  return failures == 0 ? 0 : 1;
}
