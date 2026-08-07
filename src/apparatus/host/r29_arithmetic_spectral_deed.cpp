#include <fstream>
#include <memory>

#include <holonics/apparatus/arithmetic_spectral_executor.hpp>
#include <holonics/apparatus/arithmetic_spectral_store_adapter.hpp>
#include <holonics/event/hodge_realization_rest.hpp>

#include "r29_artifact.hpp"
#include "r29_atlas.hpp"
#include "r29_cases.hpp"
#include "r29_verify.hpp"

int main(int argc, char** argv) {
  if (argc != 14) { return 2; }
  holonics::organ::arithmetic_spectral_card card{};
  holonics::event::hodge_realization_rest_record inherited{};
  const auto card_load = holonics::apparatus::read_arithmetic_spectral_card(argv[4], card);
  const auto rest_load = holonics::apparatus::read_hodge_spectral_handoff(argv[2], inherited);
  const bool source_loaded = card_load.returned();
  if (!source_loaded || !rest_load.returned()) { return 3; }
  const auto mount = holonics::tests::r29_case(inherited, card);
  const holonics::apparatus::lean_process_configuration process{
      argv[9], argv[10], argv[11], argv[5], argv[6], argv[7], argv[8], argv[12]};
  holonics::event::arithmetic_spectral_observation observation{};
  auto workspace = std::make_unique<holonics::organ::arithmetic_spectral_workspace>();
  holonics::event::arithmetic_spectral_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_arithmetic_spectral(
      mount, process, observation, *workspace, handoff);
  const auto rest_write = holonics::apparatus::write_arithmetic_spectral_handoff(argv[3], handoff);
  const auto failures = holonics::tests::r29_verification_failures(source_loaded, rest_load,
      execution, observation, *workspace, handoff) + !rest_write.returned();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  std::ofstream atlas{argv[13], std::ios::binary | std::ios::trunc};
  if (!deed || !atlas) { return 4; }
  holonics::tests::write_r29_artifact(deed, source_loaded, card_load, rest_load, rest_write,
      execution, observation, handoff, failures);
  holonics::tests::write_r29_atlas(atlas, observation, *workspace);
  return failures == 0 ? 0 : 1;
}
