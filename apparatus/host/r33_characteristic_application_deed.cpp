#include <fstream>

#include <holonics/apparatus/characteristic_hypergeometry_executor.hpp>
#include <holonics/apparatus/characteristic_hypergeometry_store_adapter.hpp>

namespace {
std::size_t
failures(const holonics::apparatus::characteristic_executor_receipt &e,
         const holonics::event::heldout_characteristic_observation &o,
         const holonics::event::characteristic_hypergeometry_rest_record &r) {
  std::size_t f = 0;
  auto c = [&f](bool b) { f += b; };
  c(!e.returned());
  c(!o.inquiry.theory_formed);
  c(!o.inquiry.prediction_before_comparison);
  c(!o.inquiry.development_sources_absent);
  c(o.inquiry.visible[0] != 3 || o.inquiry.visible[1] != 2 ||
    o.inquiry.visible[2] != 4);
  c(o.inquiry.predicted_trace != 3 || o.inquiry.source_trace != 3);
  c(o.inquiry.predicted_discriminant != 5 || o.inquiry.characteristic[0] != 1 ||
    o.inquiry.characteristic[1] != -3 || o.inquiry.characteristic[2] != 1);
  c(o.inquiry.predicted_fixed_rank != 0);
  c(o.inquiry.exclusion !=
    holonics::organ::hypergeometry_trace_obstruction::organ_absent);
  c(o.inquiry.changed !=
    holonics::organ::hypergeometry_trace_obstruction::unsupported_determinant);
  c(!o.inquiry.ablation_exact || !o.inquiry.improved);
  c(o.passage.typed.state != holonics::event::checker_return_status::accepted);
  c(!o.rest.returned || !o.remount.application_preserved ||
    !o.handoff.returned);
  c(!o.final_can_continue || o.final_head.value() != 14'001'048 ||
    o.final_continuation.value() != 15'001'048);
  c(!r.applied || !r.application.accepted ||
    r.application.identity.value() != 200'302);
  c(r.standing.standing.standing.body.regions[0].morphology != 1199);
  c(r.standing.standing.standing.mathematical_morphology != 418 ||
    r.standing.standing.standing.codec_morphology != 195);
  c(r.integrity != holonics::event::characteristic_rest_integrity(r));
  return f;
}
void matrix(std::ostream &out, const holonics::organ::exact_matrix2 &m) {
  for (const auto value : m.value)
    out << '\t' << value;
}
void atlas(std::ostream &out,
           const holonics::organ::heldout_characteristic_receipt &r) {
  out << "face\ta\tb\tc\td\tvalue\n";
  out << "A";
  matrix(out, r.first);
  out << "\t-\nB";
  matrix(out, r.second);
  out << "\t-\nAB";
  matrix(out, r.product);
  out << "\t-\nC";
  matrix(out, r.closed);
  out << "\t" << r.source_trace << "\nvisible\t0\t0\t0\t0\t" << r.visible[0]
      << ',' << r.visible[1] << ',' << r.visible[2]
      << "\npredicted\t0\t0\t0\t0\t" << r.predicted_trace
      << "\ndiscriminant\t0\t0\t0\t0\t" << r.predicted_discriminant
      << "\ncharacteristic\t0\t0\t0\t0\t" << r.characteristic[0] << ','
      << r.characteristic[1] << ',' << r.characteristic[2]
      << "\ncontrol_exclusion\t0\t0\t0\t0\t"
      << static_cast<unsigned>(r.exclusion)
      << "\ncontrol_determinant\t0\t0\t0\t0\t"
      << static_cast<unsigned>(r.changed) << '\n';
}
} // namespace
int main(int argc, char **argv) {
  if (argc != 15)
    return 2;
  holonics::apparatus::characteristic_application_mount mount{};
  const bool loaded =
      holonics::apparatus::read_characteristic_rest(argv[2], mount.inherited)
          .returned() &&
      holonics::apparatus::read_heldout_local_system_card(argv[4],
                                                          mount.heldout)
          .returned();
  if (!loaded)
    return 3;
  const holonics::apparatus::lean_process_configuration process{
      argv[9], argv[10], argv[11], argv[5],
      argv[6], argv[7],  argv[8],  argv[12]};
  holonics::event::heldout_characteristic_observation observation{};
  holonics::event::characteristic_hypergeometry_rest_record handoff{};
  const auto execution =
      holonics::apparatus::execute_characteristic_application(
          mount, process, observation, handoff);
  const auto written =
      holonics::apparatus::write_characteristic_rest(argv[3], handoff);
  const auto failed =
      failures(execution, observation, handoff) + !written.returned();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc},
      dossier{argv[13], std::ios::binary | std::ios::trunc},
      atlas_file{argv[14]};
  if (!deed || !dossier || !atlas_file)
    return 4;
  atlas(atlas_file, observation.inquiry);
  deed << "truth_status=established-bounded\n"
       << "evidence=implemented-exact,computational-witness\nformal_truth_"
          "status=proved-derived\nformal_evidence=formal-checked\nprogram=r33_"
          "characteristic_application.sm_"
       << execution.device_major << execution.device_minor
       << "\nverification_failures=" << failed
       << "\nkernel_launches=" << execution.kernel_launches.value()
       << "\nsource_currents=2\nhost_semantic_events=0\ndevelopment_card_"
          "arguments=0\nprediction_before_comparison="
       << observation.inquiry.prediction_before_comparison
       << "\nvisible=" << observation.inquiry.visible[0] << ','
       << observation.inquiry.visible[1] << ','
       << observation.inquiry.visible[2]
       << "\npredicted_closed_trace=" << observation.inquiry.predicted_trace
       << "\nsource_closed_trace=" << observation.inquiry.source_trace
       << "\nfinal_rest_bytes=" << sizeof(handoff)
       << "\nfinal_body=head:" << observation.final_head.value()
       << ",continuation:" << observation.final_continuation.value()
       << ",morphology:"
       << handoff.standing.standing.standing.body.regions[0].morphology
       << ",mathematical:"
       << handoff.standing.standing.standing.mathematical_morphology
       << ",codec:" << handoff.standing.standing.standing.codec_morphology
       << ",transport:" << handoff.transport_morphology
       << "\nchecker_exit=" << observation.passage.raw.exit_status
       << "\nformal_begin\n";
  deed.write(observation.passage.formal.bytes,
             observation.passage.formal.byte_count);
  deed << "formal_end\nconversation_begin\n";
  deed.write(observation.dossier.bytes, observation.dossier.byte_count);
  deed << "\nconversation_end\nphysical_telemetry=engine_time:unknown,checker_"
          "time:unknown,energy:unknown\n";
  dossier.write(observation.dossier.bytes, observation.dossier.byte_count);
  return failed == 0 ? 0 : 1;
}
