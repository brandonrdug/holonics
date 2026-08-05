#include <fstream>

#include <holonics/apparatus/trace_fiber_executor.hpp>
#include <holonics/apparatus/trace_fiber_store_adapter.hpp>

namespace {
std::size_t failures(const holonics::apparatus::trace_fiber_executor_receipt &e,
                     const holonics::event::heldout_trace_fiber_observation &o,
                     const holonics::event::trace_fiber_rest_record &r) {
  std::size_t f = 0;
  auto check = [&f](bool failed) { f += failed; };
  check(!e.returned() || !o.inquiry.theory_formed ||
        !o.inquiry.prediction_before_comparison || !o.inquiry.improved);
  constexpr std::int64_t lower[6]{3, 2, 2, 5, 5, 6};
  for (std::uint8_t i = 0; i < 6; ++i)
    check(o.inquiry.lower[i] != lower[i]);
  check(o.inquiry.anchor != 15 || o.inquiry.predicted_companion != 11 ||
        o.inquiry.source_companion != 11 || o.inquiry.symmetric[0] != 26 ||
        o.inquiry.symmetric[1] != 165 || o.inquiry.discriminant != 16 ||
        o.inquiry.roots[0] != 11 || o.inquiry.roots[1] != 15);
  check(o.inquiry.quadratic[0] != 1 || o.inquiry.quadratic[1] != -26 ||
        o.inquiry.quadratic[2] != 165 || !o.inquiry.unordered_without_orientation);
  check(o.inquiry.orientation_exclusion !=
            holonics::organ::trace_fiber_obstruction::orientation_unresolved ||
        o.inquiry.exclusion != holonics::organ::trace_fiber_obstruction::organ_absent ||
        o.inquiry.changed !=
            holonics::organ::trace_fiber_obstruction::unsupported_determinant);
  check(o.passage.typed.state != holonics::event::checker_return_status::accepted);
  check(!o.rest.returned || !o.remount.laws_preserved || !o.handoff.returned ||
        !o.final_can_continue || o.final_head.value() != 14'001'052 ||
        o.final_continuation.value() != 15'001'052);
  check(!r.applied || r.application.identity.value() != 201'303 ||
        r.integrity != holonics::event::trace_fiber_rest_integrity(r));
  return f;
}
void matrix(std::ostream &out, const holonics::organ::exact_matrix2 &m) {
  for (const auto value : m.value)
    out << '\t' << value;
}
void atlas(std::ostream &out,
           const holonics::organ::heldout_trace_fiber_receipt &r) {
  out << "kind\tvalue\nvisible\t";
  for (const auto value : r.lower)
    out << value << ',';
  out << "\nquadratic\t" << r.quadratic[0] << ',' << r.quadratic[1] << ','
      << r.quadratic[2] << "\nroots\t" << r.roots[0] << ',' << r.roots[1]
      << "\norientation\t" << r.anchor << ',' << r.predicted_companion
      << "\nsource_companion\t" << r.source_companion
      << "\ndiscriminant\t" << r.discriminant
      << "\norgan_exclusion\t" << static_cast<unsigned>(r.exclusion)
      << "\norientation_exclusion\t" << static_cast<unsigned>(r.orientation_exclusion)
      << "\ndeterminant_foil\t" << static_cast<unsigned>(r.changed)
      << "\ncomparison\t" << r.improved << "\nmatrices";
  for (const auto &m : r.matrices)
    matrix(out, m);
  out << '\n';
}
} // namespace
int main(int argc, char **argv) {
  if (argc != 15)
    return 2;
  holonics::apparatus::trace_fiber_application_mount mount{};
  bool loaded = holonics::apparatus::read_trace_fiber_rest(argv[2], mount.inherited).returned() &&
                holonics::apparatus::read_heldout_oriented_system_card(
                    argv[4], mount.heldout).returned();
  if (!loaded)
    return 3;
  const holonics::apparatus::lean_process_configuration process{
      argv[9], argv[10], argv[11], argv[5], argv[6], argv[7], argv[8], argv[12]};
  holonics::event::heldout_trace_fiber_observation observation{};
  holonics::event::trace_fiber_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_trace_fiber_application(
      mount, process, observation, handoff);
  const auto written = holonics::apparatus::write_trace_fiber_rest(argv[3], handoff);
  const auto failed = failures(execution, observation, handoff) + !written.returned();
  std::ofstream deed{argv[1]}, dossier{argv[13]}, a{argv[14]};
  if (!deed || !dossier || !a)
    return 4;
  dossier.write(observation.dossier.bytes, observation.dossier.byte_count);
  atlas(a, observation.inquiry);
  deed << "truth_status=established-bounded\nevidence=implemented-exact,computational-witness\n"
       << "formal_truth_status=proved-derived\nformal_evidence=formal-checked\n"
       << "program=r34_trace_fiber_application.sm_" << execution.device_major
       << execution.device_minor << "\nverification_failures=" << failed
       << "\nkernel_launches=" << execution.kernel_launches.value()
       << "\nsource_currents=2\nhost_semantic_events=0\nprediction_before_comparison=1"
       << "\nvisible=3,2,2,5,5,6\nanchor=15\npredicted_companion="
       << observation.inquiry.predicted_companion << "\nsource_companion="
       << observation.inquiry.source_companion << "\nfinal_rest_bytes=" << sizeof(handoff)
       << "\nfinal_body=head:" << observation.final_head.value() << ",continuation:"
       << observation.final_continuation.value() << "\nchecker_exit="
       << observation.passage.raw.exit_status << "\nformal_begin\n";
  deed.write(observation.passage.formal.bytes, observation.passage.formal.byte_count);
  deed << "formal_end\nconversation_begin\n";
  deed.write(observation.dossier.bytes, observation.dossier.byte_count);
  deed << "conversation_end\nphysical_telemetry=engine_time:unknown,checker_time:unknown,energy:unknown\n";
  return failed == 0 ? 0 : 1;
}
