#include <fstream>
#include <memory>

#include <holonics/apparatus/rederivation_executor.hpp>
#include <holonics/apparatus/rederivation_store_adapter.hpp>

#include "r30_artifact.hpp"
#include "r30_atlas.hpp"
#include "r30_cases.hpp"
#include "r30_verify.hpp"

int main(int argc, char **argv) {
  if (argc != 21)
    return 2;
  holonics::organ::matching_problem_card matching{};
  holonics::organ::lattice_problem_card lattice{};
  holonics::organ::cover_problem_card cover{};
  holonics::event::arithmetic_spectral_rest_record inherited{};
  holonics::apparatus::rederivation_store_receipt cards[3]{
      holonics::apparatus::read_matching_problem_card(argv[4], matching),
      holonics::apparatus::read_lattice_problem_card(argv[5], lattice),
      holonics::apparatus::read_cover_problem_card(argv[6], cover)};
  const auto rest_load =
      holonics::apparatus::read_arithmetic_rederivation_handoff(argv[2],
                                                                inherited);
  const bool loaded =
      cards[0].returned() && cards[1].returned() && cards[2].returned();
  if (!loaded || !rest_load.returned())
    return 3;
  const auto mount =
      holonics::tests::r30_case(inherited, matching, lattice, cover);
  const holonics::apparatus::rederivation_process_configuration process{
      {argv[15], argv[16], argv[17], argv[11], argv[12], argv[13], argv[14],
       argv[18]},
      {argv[15], argv[16], argv[17], argv[7], argv[8], argv[9], argv[10],
       argv[18]}};
  holonics::event::rederivation_observation observation{};
  auto workspace = std::make_unique<holonics::organ::rederivation_workspace>();
  holonics::event::rederivation_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_rederivation(
      mount, process, observation, *workspace, handoff);
  const auto rest_write =
      holonics::apparatus::write_rederivation_handoff(argv[3], handoff);
  const auto failures =
      holonics::tests::r30_verification_failures(
          loaded, rest_load, execution, observation, *workspace, handoff) +
      !rest_write.returned();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc},
      atlas{argv[19], std::ios::binary | std::ios::trunc},
      dossier{argv[20], std::ios::binary | std::ios::trunc};
  if (!deed || !atlas || !dossier)
    return 4;
  holonics::tests::write_r30_artifact(deed, loaded, cards, rest_load,
                                      rest_write, execution, observation,
                                      handoff, failures);
  holonics::tests::write_r30_atlas(atlas, observation, *workspace);
  dossier.write(observation.passage.conversational.bytes,
                observation.passage.conversational.byte_count);
  return failures == 0 ? 0 : 1;
}
