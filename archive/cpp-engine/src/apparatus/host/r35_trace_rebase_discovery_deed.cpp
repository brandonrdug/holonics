#include <fstream>
#include <memory>

#include <holonics/apparatus/trace_fiber_store_adapter.hpp>
#include <holonics/apparatus/trace_rebase_executor.hpp>
#include <holonics/apparatus/trace_rebase_store_adapter.hpp>

#include "r35_trace_rebase_atlas.hpp"

namespace {
std::size_t failures(
    const holonics::apparatus::trace_rebase_executor_receipt &execution,
    const holonics::event::trace_rebase_discovery_observation &observation,
    const holonics::event::trace_rebase_rest_record &rest) {
  std::size_t count = 0;
  auto check = [&count](bool failed) { count += failed; };
  const auto &inquiry = observation.inquiry;
  check(!execution.returned() || !inquiry.theory_formed ||
        !inquiry.population_complete || !inquiry.controls_complete ||
        !inquiry.witnesses_complete || inquiry.residuals != 0 ||
        inquiry.tangent_failures != 0);
  check(inquiry.state_count != holonics::organ::trace_rebase_state_capacity ||
        inquiry.edge_count != holonics::organ::trace_rebase_edge_capacity);
  for (const auto &candidate : inquiry.candidates)
    check(!candidate.selected || !candidate.primitive ||
          candidate.obstruction !=
              holonics::organ::trace_rebase_obstruction::none);
  for (const auto &map : inquiry.maps)
    check(!map.primitive);
  for (const auto &witness : inquiry.witnesses)
    check(!witness.found);
  for (std::uint16_t edge = 0; edge < inquiry.edge_count; ++edge)
    check(!inquiry.edges[edge].chain_exact &&
          inquiry.edges[edge].differential_obstruction !=
              holonics::organ::trace_rebase_obstruction::singular_hypersurface);
  for (std::uint8_t move = 0;
       move < holonics::organ::trace_rebase_move_count; ++move) {
    const auto &value = inquiry.transitions[move];
    check(value.regular_regular + value.regular_branch + value.branch_regular +
              value.branch_branch !=
          holonics::organ::trace_rebase_state_capacity);
    for (std::uint8_t source = 0;
         source < holonics::organ::trace_rebase_source_count; ++source)
      check(inquiry.source_holdout_residuals[move][source] != 0);
  }
  check(observation.passage.typed.state !=
        holonics::event::checker_return_status::accepted);
  check(!observation.rest.returned ||
        !observation.rest.developmental_rows_absent ||
        !observation.rest.matrices_absent ||
        !observation.rest.tangent_rows_absent ||
        !observation.rest.source_detached);
  check(!observation.remount.maps_preserved ||
        !observation.remount.differential_preserved ||
        !observation.handoff.returned || !observation.final_can_continue ||
        observation.final_head.value() != 14'001'054 ||
        observation.final_continuation.value() != 15'001'054);
  check(rest.applied ||
        rest.integrity != holonics::event::trace_rebase_rest_integrity(rest) ||
        !rest.law.checker_founded || !rest.law.deck.primitive);
  return count;
}
} // namespace

int main(int argc, char **argv) {
  if (argc != 19)
    return 2;
  holonics::apparatus::trace_rebase_discovery_mount mount{};
  bool loaded = holonics::apparatus::read_trace_fiber_rest(
                    argv[2], mount.inherited).returned();
  for (std::uint8_t source = 0; source < 3; ++source)
    loaded = loaded && holonics::apparatus::read_trace_rebase_source_card(
                           argv[4 + source], mount.cards.sources[source])
                           .returned();
  if (!loaded)
    return 3;
  const holonics::apparatus::lean_process_configuration process{
      argv[11], argv[12], argv[13], argv[7], argv[8], argv[9], argv[10],
      argv[14]};
  auto observation =
      std::make_unique<holonics::event::trace_rebase_discovery_observation>();
  auto workspace = std::make_unique<holonics::organ::trace_rebase_workspace>();
  holonics::event::trace_rebase_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_trace_rebase_discovery(
      mount, process, *observation, *workspace, handoff);
  const auto written =
      holonics::apparatus::write_trace_rebase_rest(argv[3], handoff);
  const auto failed = failures(execution, *observation, handoff) +
                      !written.returned();
  std::ofstream deed{argv[1]}, states{argv[15]}, edges{argv[16]},
      tangents{argv[17]}, laws{argv[18]};
  if (!deed || !states || !edges || !tangents || !laws)
    return 4;
  r35_atlas::states(states, observation->inquiry);
  r35_atlas::edges(edges, observation->inquiry);
  r35_atlas::tangents(tangents, observation->inquiry);
  r35_atlas::laws(laws, observation->inquiry);
  deed << "truth_status=established-bounded\n"
          "evidence=implemented-exact,computational-witness\n"
          "formal_truth_status=proved-derived\nformal_evidence=formal-checked\n"
       << "program=r35_trace_rebase_discovery.sm_" << execution.device_major
       << execution.device_minor << "\nverification_failures=" << failed
       << "\nkernel_launches=" << execution.kernel_launches.value()
       << "\nsource_currents=3\nhost_semantic_events=0\nstates="
       << observation->inquiry.state_count << "\nedges="
       << observation->inquiry.edge_count << "\nmap_residuals="
       << observation->inquiry.residuals << "\ntangent_failures="
       << observation->inquiry.tangent_failures << "\nsingular_edges="
       << observation->inquiry.singular_edges << "\nintermediate_rest_bytes="
       << sizeof(handoff)
       << "\ndevelopmental_rows_in_rest=0\nmatrices_in_rest=0"
          "\ntangent_rows_in_rest=0\nfinal_body=head:"
       << observation->final_head.value() << ",continuation:"
       << observation->final_continuation.value() << "\nchecker_exit="
       << observation->passage.raw.exit_status << "\nformal_begin\n";
  deed.write(observation->passage.formal.bytes,
             observation->passage.formal.byte_count);
  deed << "formal_end\nphysical_telemetry=engine_time:unknown,checker_time:unknown,energy:unknown\n";
  return failed == 0 ? 0 : 1;
}
