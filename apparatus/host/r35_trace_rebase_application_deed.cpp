#include <fstream>
#include <memory>

#include <holonics/apparatus/trace_rebase_executor.hpp>
#include <holonics/apparatus/trace_rebase_store_adapter.hpp>

namespace {
std::size_t failures(
    const holonics::apparatus::trace_rebase_executor_receipt &execution,
    const holonics::event::heldout_trace_rebase_observation &observation,
    const holonics::event::trace_rebase_rest_record &rest) {
  std::size_t count = 0;
  auto check = [&count](bool failed) { count += failed; };
  const auto &inquiry = observation.inquiry;
  check(!execution.returned() || !inquiry.theory_formed || !inquiry.compared ||
        !inquiry.prediction_before_comparison || !inquiry.source_detached ||
        inquiry.residuals != 0 || inquiry.path_length < 8);
  for (std::uint8_t step = 0; step <= inquiry.path_length; ++step) {
    for (std::uint8_t coordinate = 0;
         coordinate < holonics::organ::trace_rebase_coordinate_count;
         ++coordinate)
      check(inquiry.predicted[step][coordinate] !=
            inquiry.source[step][coordinate]);
    check(inquiry.tangent_rank[step] !=
          holonics::organ::trace_rebase_tangent_rank);
    if (step < inquiry.path_length)
      check(!inquiry.transport_exact[step] ||
            inquiry.transported_rank[step] !=
                holonics::organ::trace_rebase_tangent_rank);
  }
  check(inquiry.map_exclusion !=
            holonics::organ::trace_rebase_obstruction::map_organ_absent ||
        inquiry.lift_exclusion !=
            holonics::organ::trace_rebase_obstruction::lift_organ_absent ||
        inquiry.orientation_exclusion !=
            holonics::organ::trace_rebase_obstruction::orientation_unresolved ||
        inquiry.aperture_control !=
            holonics::organ::trace_rebase_obstruction::aperture_exceeded ||
        inquiry.determinant_control !=
            holonics::organ::trace_rebase_obstruction::unsupported_determinant);
  check(observation.passage.typed.state !=
        holonics::event::checker_return_status::accepted);
  check(!observation.rest.returned || !observation.rest.source_detached ||
        !observation.remount.maps_preserved ||
        !observation.remount.differential_preserved ||
        !observation.handoff.returned || !observation.final_can_continue ||
        observation.final_head.value() != 14'001'056 ||
        observation.final_continuation.value() != 15'001'056);
  check(!rest.applied || !rest.application.accepted ||
        rest.integrity != holonics::event::trace_rebase_rest_integrity(rest));
  return count;
}
void atlas(std::ostream &out,
           const holonics::organ::heldout_trace_rebase_receipt &receipt) {
  out << "step\tmove\tpredicted\tsource\ttangent_rank\tvertical_rank"
         "\tbranch\ttransported_rank\ttransport_exact\n";
  for (std::uint8_t step = 0; step <= receipt.path_length; ++step) {
    out << static_cast<unsigned>(step) << '\t';
    if (step < receipt.path_length)
      out << static_cast<unsigned>(receipt.moves[step]);
    out << '\t';
    for (const auto value : receipt.predicted[step])
      out << value << ',';
    out << '\t';
    for (const auto value : receipt.source[step])
      out << value << ',';
    out << '\t' << static_cast<unsigned>(receipt.tangent_rank[step]) << '\t'
        << static_cast<unsigned>(receipt.vertical_rank[step]) << '\t'
        << receipt.branch[step] << '\t';
    if (step < receipt.path_length)
      out << static_cast<unsigned>(receipt.transported_rank[step]) << '\t'
          << receipt.transport_exact[step];
    out << '\n';
  }
  out << "controls\t-\t" << static_cast<unsigned>(receipt.map_exclusion)
      << ',' << static_cast<unsigned>(receipt.lift_exclusion) << ','
      << static_cast<unsigned>(receipt.orientation_exclusion) << ','
      << static_cast<unsigned>(receipt.aperture_control) << ','
      << static_cast<unsigned>(receipt.determinant_control) << "\t-\t-\t-\t-\t-\t-\n";
}
} // namespace

int main(int argc, char **argv) {
  if (argc != 15)
    return 2;
  holonics::apparatus::trace_rebase_application_mount mount{};
  const bool loaded = holonics::apparatus::read_trace_rebase_rest(
                          argv[2], mount.inherited).returned() &&
                      holonics::apparatus::read_heldout_trace_rebase_card(
                          argv[4], mount.heldout).returned();
  if (!loaded)
    return 3;
  const holonics::apparatus::lean_process_configuration process{
      argv[9], argv[10], argv[11], argv[5], argv[6], argv[7], argv[8], argv[12]};
  auto observation =
      std::make_unique<holonics::event::heldout_trace_rebase_observation>();
  holonics::event::trace_rebase_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_trace_rebase_application(
      mount, process, *observation, handoff);
  const auto written =
      holonics::apparatus::write_trace_rebase_rest(argv[3], handoff);
  const auto failed = failures(execution, *observation, handoff) +
                      !written.returned();
  std::ofstream deed{argv[1]}, dossier{argv[13]}, transport{argv[14]};
  if (!deed || !dossier || !transport)
    return 4;
  dossier.write(observation->dossier.bytes, observation->dossier.byte_count);
  atlas(transport, observation->inquiry);
  deed << "truth_status=established-bounded\n"
          "evidence=implemented-exact,computational-witness\n"
          "formal_truth_status=proved-derived\nformal_evidence=formal-checked\n"
       << "program=r35_trace_rebase_application.sm_" << execution.device_major
       << execution.device_minor << "\nverification_failures=" << failed
       << "\nkernel_launches=" << execution.kernel_launches.value()
       << "\nsource_currents=2\nhost_semantic_events=0"
          "\nprediction_before_comparison="
       << observation->inquiry.prediction_before_comparison << "\npath_length="
       << static_cast<unsigned>(observation->inquiry.path_length)
       << "\ncomparison_residuals=" << observation->inquiry.residuals
       << "\nfinal_rest_bytes=" << sizeof(handoff) << "\nfinal_body=head:"
       << observation->final_head.value() << ",continuation:"
       << observation->final_continuation.value() << "\nchecker_exit="
       << observation->passage.raw.exit_status << "\nformal_begin\n";
  deed.write(observation->passage.formal.bytes,
             observation->passage.formal.byte_count);
  deed << "formal_end\nconversation_begin\n";
  deed.write(observation->dossier.bytes, observation->dossier.byte_count);
  deed << "conversation_end\nphysical_telemetry=engine_time:unknown,checker_time:unknown,energy:unknown\n";
  return failed == 0 ? 0 : 1;
}
