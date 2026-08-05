#include <fstream>

#include <holonics/apparatus/expression_geometry_executor.hpp>
#include <holonics/apparatus/expression_geometry_store_adapter.hpp>
#include <holonics/event/intrinsic_hypergeometry_rest.hpp>

#include "r27_artifact.hpp"
#include "r27_atlas.hpp"
#include "r27_cases.hpp"
#include "r27_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 14) { return 2; }
  holonics::organ::expression_geometry_card card{};
  holonics::event::intrinsic_hypergeometry_rest_record inherited{};
  const auto card_load = holonics::apparatus::read_expression_geometry_card(argv[4], card);
  const auto rest_load = holonics::apparatus::read_intrinsic_hypergeometry_handoff(
      argv[2], inherited);
  const bool source_loaded = card_load.returned();
  if (!source_loaded || !rest_load.returned()) { return 3; }
  const auto mount = holonics::tests::r27_case(inherited, card);
  const holonics::apparatus::lean_process_configuration process{
      argv[9], argv[10], argv[11], argv[5], argv[6], argv[7], argv[8], argv[12]};
  holonics::event::expression_geometry_observation observation{};
  holonics::event::expression_geometry_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_expression_geometry(
      mount, process, observation, handoff);
  const auto rest_write = holonics::apparatus::write_expression_geometry_handoff(argv[3], handoff);
  const auto failures = holonics::tests::r27_verification_failures(source_loaded, rest_load,
      execution, observation, handoff) + !rest_write.returned();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  std::ofstream atlas{argv[13], std::ios::binary | std::ios::trunc};
  if (!deed || !atlas) { return 4; }
  holonics::tests::write_r27_artifact(deed, source_loaded, card_load, rest_load, rest_write,
      execution, observation, handoff, failures);
  holonics::tests::write_r27_atlas(atlas, observation);
  return failures == 0 ? 0 : 1;
}
