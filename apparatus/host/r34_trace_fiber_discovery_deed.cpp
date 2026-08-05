#include <fstream>

#include <holonics/apparatus/characteristic_hypergeometry_store_adapter.hpp>
#include <holonics/apparatus/trace_fiber_executor.hpp>
#include <holonics/apparatus/trace_fiber_store_adapter.hpp>

namespace {
void matrix(std::ostream &out, const holonics::organ::exact_matrix2 &m) {
  for (const auto value : m.value)
    out << '\t' << value;
}
std::size_t failures(const holonics::apparatus::trace_fiber_executor_receipt &e,
                     const holonics::event::trace_fiber_discovery_observation &o,
                     const holonics::event::trace_fiber_rest_record &r) {
  std::size_t f = 0;
  auto check = [&f](bool failed) { f += failed; };
  check(!e.returned() || !o.inquiry.theory_formed ||
        !o.inquiry.census_complete || !o.inquiry.witnesses_complete);
  for (std::uint8_t i = 0; i < 3; ++i)
    check(o.inquiry.words[i].count != 12 ||
          o.inquiry.triple_count[i] != 1'728);
  check(o.inquiry.group_count != 2'072 ||
        o.inquiry.branch_count != 2'580 ||
        o.inquiry.two_sheet_count != 2'604 || o.inquiry.residuals != 0);
  check(o.inquiry.candidates[3].rank != 84 ||
        o.inquiry.candidates[3].nullity != 1 ||
        o.inquiry.candidates[7].rank != 84 ||
        o.inquiry.candidates[7].nullity != 1);
  for (std::uint8_t i = 8; i < 12; ++i)
    check(o.inquiry.candidates[i].obstruction !=
          holonics::organ::trace_fiber_obstruction::full_rank);
  check(o.inquiry.candidates[12].obstruction !=
        holonics::organ::trace_fiber_obstruction::insufficient_rows);
  check(o.inquiry.candidates[13].obstruction !=
        holonics::organ::trace_fiber_obstruction::full_rank);
  check(o.passage.typed.state != holonics::event::checker_return_status::accepted);
  check(!o.rest.returned || !o.rest.developmental_rows_absent ||
        !o.rest.target_traces_absent || !o.rest.matrices_absent);
  check(!o.remount.laws_preserved || !o.handoff.returned ||
        !o.final_can_continue || o.final_head.value() != 14'001'050 ||
        o.final_continuation.value() != 15'001'050);
  check(r.applied || r.integrity != holonics::event::trace_fiber_rest_integrity(r));
  check(r.law.organs[0].identity.value() != 201'301 ||
        r.law.organs[1].identity.value() != 201'302 ||
        !r.law.organs[0].checker_founded || !r.law.organs[1].checker_founded);
  return f;
}
void word_atlas(std::ostream &out,
                const holonics::organ::trace_fiber_discovery_receipt &r) {
  out << "source\tordinal\tlength\tletters\ta\tb\tc\td\tlineage\n";
  for (std::uint8_t s = 0; s < 3; ++s)
    for (std::uint8_t i = 0; i < r.words[s].count; ++i) {
      const auto &w = r.words[s].words[i];
      out << static_cast<unsigned>(s) << '\t' << w.ordinal << '\t'
          << static_cast<unsigned>(w.length) << '\t';
      for (std::uint8_t j = 0; j < w.length; ++j)
        out << static_cast<unsigned>(w.letters[j]);
      matrix(out, w.matrix);
      out << '\t' << w.lineage.value() << '\n';
    }
}
void triple_atlas(std::ostream &out,
                  const holonics::organ::trace_fiber_discovery_receipt &r) {
  out << "source\ta_word\tb_word\tc_word\tA\tB\tC\tAB\tAC\tBC\tABC\tACB"
         "\ta\tb\tc\td\te\tf\tp\tq\ts\tr\tdiscriminant\tgap\tbranch\n";
  for (std::uint16_t i = 0; i < holonics::organ::trace_fiber_triple_capacity; ++i) {
    const auto &t = r.triples[i];
    out << static_cast<unsigned>(t.source) << '\t' << t.words[0] << '\t'
        << t.words[1] << '\t' << t.words[2];
    for (const auto &m : t.matrices)
      matrix(out, m);
    for (const auto value : t.lower)
      out << '\t' << value;
    out << '\t' << t.ordered[0] << '\t' << t.ordered[1] << '\t'
        << t.symmetric[0] << '\t' << t.symmetric[1] << '\t'
        << t.discriminant << '\t' << t.root_gap << '\t' << t.branch << '\n';
  }
}
void group_atlas(std::ostream &out,
                 const holonics::organ::trace_fiber_discovery_receipt &r) {
  out << "a\tb\tc\td\te\tf\troot0\troot1\tbranch\tpopulation\n";
  for (std::uint16_t i = 0; i < r.group_count; ++i) {
    const auto &g = r.groups[i];
    for (const auto value : g.lower)
      out << value << '\t';
    out << g.roots[0] << '\t' << g.roots[1] << '\t' << g.branch << '\t'
        << g.population << '\n';
  }
}
void law_atlas(std::ostream &out,
               const holonics::organ::trace_fiber_discovery_receipt &r) {
  out << "kind\tindex\ttarget\tmode\trows\tfeatures\trank\tnullity\tobstruction"
         "\tselected\tvalue\n";
  for (std::uint8_t i = 0; i < holonics::organ::trace_fiber_candidate_count; ++i) {
    const auto &c = r.candidates[i];
    out << "candidate\t" << static_cast<unsigned>(i) << '\t'
        << static_cast<unsigned>(c.target) << '\t' << static_cast<unsigned>(c.mode)
        << '\t' << c.rows << '\t' << static_cast<unsigned>(c.features) << '\t'
        << static_cast<unsigned>(c.rank) << '\t' << static_cast<unsigned>(c.nullity)
        << '\t' << static_cast<unsigned>(c.obstruction) << '\t' << c.selected << '\t';
    for (const auto value : c.coefficients)
      out << value << ',';
    out << '\n';
  }
  for (std::uint8_t i = 0; i < holonics::organ::trace_fiber_witness_count; ++i)
    out << "witness\t" << static_cast<unsigned>(i) << "\t-\t-\t-\t-\t-\t-\t0\t"
        << r.witnesses[i].found << '\t' << r.witnesses[i].first << ','
        << r.witnesses[i].second << '\n';
  out << "strata\t0\t-\t-\t5184\t-\t-\t-\t0\t1\t" << r.branch_count << ','
      << r.two_sheet_count << '\n';
}
} // namespace
int main(int argc, char **argv) {
  if (argc != 19)
    return 2;
  holonics::apparatus::trace_fiber_discovery_mount mount{};
  bool loaded = holonics::apparatus::read_characteristic_rest(argv[2], mount.inherited).returned();
  for (std::uint8_t i = 0; i < 3; ++i)
    loaded = loaded && holonics::apparatus::read_three_face_source_card(
                           argv[4 + i], mount.cards.sources[i]).returned();
  if (!loaded)
    return 3;
  const holonics::apparatus::lean_process_configuration process{
      argv[11], argv[12], argv[13], argv[7], argv[8], argv[9], argv[10], argv[14]};
  holonics::event::trace_fiber_discovery_observation observation{};
  holonics::organ::trace_fiber_workspace workspace{};
  holonics::event::trace_fiber_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_trace_fiber_discovery(
      mount, process, observation, workspace, handoff);
  const auto written = holonics::apparatus::write_trace_fiber_rest(argv[3], handoff);
  const auto failed = failures(execution, observation, handoff) + !written.returned();
  std::ofstream deed{argv[1]}, a0{argv[15]}, a1{argv[16]}, a2{argv[17]}, a3{argv[18]};
  if (!deed || !a0 || !a1 || !a2 || !a3)
    return 4;
  word_atlas(a0, observation.inquiry);
  triple_atlas(a1, observation.inquiry);
  group_atlas(a2, observation.inquiry);
  law_atlas(a3, observation.inquiry);
  deed << "truth_status=established-bounded\nevidence=implemented-exact,computational-witness\n"
       << "formal_truth_status=proved-derived\nformal_evidence=formal-checked\n"
       << "program=r34_trace_fiber_discovery.sm_" << execution.device_major
       << execution.device_minor << "\nverification_failures=" << failed
       << "\nkernel_launches=" << execution.kernel_launches.value()
       << "\nsource_currents=3\nhost_semantic_events=0\nword_populations=12,12,12"
       << "\ntriple_population=5184\nfiber_groups=" << observation.inquiry.group_count
       << "\nbranch_strata=" << observation.inquiry.branch_count << ','
       << observation.inquiry.two_sheet_count << "\nlaw_residuals="
       << observation.inquiry.residuals << "\nintermediate_rest_bytes=" << sizeof(handoff)
       << "\ndevelopmental_rows_in_rest=0\ntarget_traces_in_rest=0\nmatrices_in_rest=0"
       << "\nfinal_body=head:" << observation.final_head.value() << ",continuation:"
       << observation.final_continuation.value() << "\nchecker_exit="
       << observation.passage.raw.exit_status << "\nformal_begin\n";
  deed.write(observation.passage.formal.bytes, observation.passage.formal.byte_count);
  deed << "formal_end\nphysical_telemetry=engine_time:unknown,checker_time:unknown,energy:unknown\n";
  return failed == 0 ? 0 : 1;
}
