#include <fstream>

#include <holonics/apparatus/characteristic_hypergeometry_executor.hpp>
#include <holonics/apparatus/characteristic_hypergeometry_store_adapter.hpp>
#include <holonics/apparatus/elementary_calculus_store_adapter.hpp>

namespace {
std::size_t
failures(const holonics::apparatus::characteristic_executor_receipt &e,
         const holonics::event::characteristic_discovery_observation &o,
         const holonics::event::characteristic_hypergeometry_rest_record &r) {
  std::size_t f = 0;
  auto c = [&f](bool b) { f += b; };
  c(!e.returned());
  c(!o.inquiry.theory_formed);
  c(!o.inquiry.census_complete);
  c(!o.inquiry.witnesses_complete);
  c(o.inquiry.words[0].count != 30 || o.inquiry.words[1].count != 52 ||
    o.inquiry.words[2].count != 52);
  c(o.inquiry.pair_count[0] != 900 || o.inquiry.pair_count[1] != 2704 ||
    o.inquiry.pair_count[2] != 2704);
  c(o.inquiry.group_count != 281);
  c(o.inquiry.closed_strata[0] != 0 || o.inquiry.closed_strata[1] != 440 ||
    o.inquiry.closed_strata[2] != 5868);
  constexpr std::int64_t expected[21]{2, 0, 0, 0, -1, 0, 0, -1, 0, -1, 0,
                                      0, 0, 0, 1, 0,  0, 0, 0,  0, 1};
  for (std::uint8_t i = 0; i < 21; ++i)
    c(o.inquiry.organ.coefficients[i] != expected[i]);
  c(o.inquiry.law_residuals != 0);
  c(o.inquiry.candidates[3].obstruction !=
    holonics::organ::hypergeometry_trace_obstruction::none);
  c(o.inquiry.candidates[4].obstruction !=
    holonics::organ::hypergeometry_trace_obstruction::full_rank);
  c(o.inquiry.candidates[5].obstruction !=
    holonics::organ::hypergeometry_trace_obstruction::full_rank);
  c(o.inquiry.candidates[6].obstruction !=
    holonics::organ::hypergeometry_trace_obstruction::insufficient_rows);
  c(o.passage.typed.state != holonics::event::checker_return_status::accepted);
  c(!o.rest.returned || !o.rest.developmental_rows_absent ||
    !o.rest.matrices_absent);
  c(!o.remount.law_preserved || !o.handoff.returned || !o.final_can_continue);
  c(o.final_head.value() != 14'001'046 ||
    o.final_continuation.value() != 15'001'046);
  c(r.applied);
  c(r.integrity != holonics::event::characteristic_rest_integrity(r));
  c(r.law.organ.identity.value() != 200'301 || !r.law.organ.checker_founded);
  return f;
}
void matrix(std::ostream &out, const holonics::organ::exact_matrix2 &m) {
  for (const auto value : m.value)
    out << '\t' << value;
}
void word_atlas(
    std::ostream &out,
    const holonics::organ::characteristic_hypergeometry_receipt &r) {
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
void pair_atlas(
    std::ostream &out,
    const holonics::organ::characteristic_hypergeometry_receipt &r) {
  out << "source\tleft\tright\tA\tB\tAB\tC\tx\ty\tz\tk\tdx\tdy\tdz\tdk\tsx\tsy"
         "\tsz\tsk\trA\trB\trAB\trC\n";
  for (std::uint8_t s = 0; s < 3; ++s) {
    const auto base = holonics::organ::characteristic_census_detail::offset(s);
    for (std::uint16_t i = 0; i < r.pair_count[s]; ++i) {
      const auto &p = r.pairs[base + i];
      out << static_cast<unsigned>(s) << '\t' << p.left_word << '\t'
          << p.right_word;
      matrix(out, p.first);
      matrix(out, p.second);
      matrix(out, p.product);
      matrix(out, p.closed);
      out << '\t' << p.trace_first << '\t' << p.trace_second << '\t'
          << p.trace_product << '\t' << p.trace_closed;
      for (const auto value : p.discriminants)
        out << '\t' << value;
      for (const auto value : p.strata)
        out << '\t' << static_cast<int>(value);
      for (const auto value : p.fixed_ranks)
        out << '\t' << static_cast<unsigned>(value);
      out << '\n';
    }
  }
}
void group_atlas(
    std::ostream &out,
    const holonics::organ::characteristic_hypergeometry_receipt &r) {
  out << "x\ty\tz\tk\tsx\tsy\tsz\tsk\tfixed\tpopulation\n";
  for (std::uint16_t i = 0; i < r.group_count; ++i) {
    const auto &g = r.groups[i];
    for (const auto value : g.coordinates)
      out << value << '\t';
    for (const auto value : g.strata)
      out << static_cast<int>(value) << '\t';
    out << static_cast<unsigned>(g.closed_fixed_rank) << '\t' << g.population
        << '\n';
  }
}
void law_atlas(std::ostream &out,
               const holonics::organ::characteristic_hypergeometry_receipt &r) {
  out << "kind\tindex\trows\tfeatures\trank\tnullity\tobstruction\tselected\tva"
         "lue\n";
  for (std::uint8_t i = 0; i < 7; ++i) {
    const auto &c = r.candidates[i];
    out << "candidate\t" << static_cast<unsigned>(i) << '\t' << c.rows << '\t'
        << static_cast<unsigned>(c.features) << '\t'
        << static_cast<unsigned>(c.rank) << '\t'
        << static_cast<unsigned>(c.nullity) << '\t'
        << static_cast<unsigned>(c.obstruction) << '\t' << c.selected << '\t';
    for (const auto value : c.coefficients)
      out << value << ',';
    out << '\n';
  }
  for (std::uint8_t i = 0; i < 5; ++i) {
    const auto &w = r.witnesses[i];
    out << "witness\t" << static_cast<unsigned>(i) << "\t-\t-\t-\t-\t0\t"
        << w.found << '\t' << w.first_pair << ',' << w.second_pair << '\n';
  }
  out << "strata\tclosed\t-\t-\t-\t-\t0\t1\t" << r.closed_strata[0] << ','
      << r.closed_strata[1] << ',' << r.closed_strata[2] << '\n';
}
} // namespace
int main(int argc, char **argv) {
  if (argc != 19)
    return 2;
  holonics::apparatus::characteristic_discovery_mount mount{};
  bool loaded = holonics::apparatus::read_elementary_calculus_rest(
                    argv[2], mount.inherited)
                    .returned();
  for (std::uint8_t i = 0; i < 3; ++i)
    loaded = loaded && holonics::apparatus::read_transition_source_card(
                           argv[4 + i], mount.cards.sources[i])
                           .returned();
  if (!loaded)
    return 3;
  const holonics::apparatus::lean_process_configuration process{
      argv[11], argv[12], argv[13], argv[7],
      argv[8],  argv[9],  argv[10], argv[14]};
  holonics::event::characteristic_discovery_observation observation{};
  holonics::organ::characteristic_workspace workspace{};
  holonics::event::characteristic_hypergeometry_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_characteristic_discovery(
      mount, process, observation, workspace, handoff);
  const auto written =
      holonics::apparatus::write_characteristic_rest(argv[3], handoff);
  const auto failed =
      failures(execution, observation, handoff) + !written.returned();
  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc}, a0{argv[15]},
      a1{argv[16]}, a2{argv[17]}, a3{argv[18]};
  if (!deed || !a0 || !a1 || !a2 || !a3)
    return 4;
  word_atlas(a0, observation.inquiry);
  pair_atlas(a1, observation.inquiry);
  group_atlas(a2, observation.inquiry);
  law_atlas(a3, observation.inquiry);
  deed << "truth_status=established-bounded\nevidence=implemented-exact,"
          "computational-witness\n"
       << "formal_truth_status=proved-derived\nformal_evidence=formal-"
          "checked\nprogram=r33_characteristic_discovery.sm_"
       << execution.device_major << execution.device_minor
       << "\nverification_failures=" << failed
       << "\nkernel_launches=" << execution.kernel_launches.value()
       << "\nsource_currents=3\nhost_semantic_events=0\n"
       << "word_populations=30,52,52\npair_population=6308\narchetype_groups="
       << observation.inquiry.group_count
       << "\nclosed_strata=" << observation.inquiry.closed_strata[0] << ','
       << observation.inquiry.closed_strata[1] << ','
       << observation.inquiry.closed_strata[2]
       << "\nlaw_residuals=" << observation.inquiry.law_residuals
       << "\nintermediate_rest_bytes=" << sizeof(handoff)
       << "\ndevelopmental_rows_in_rest=0\nmatrices_in_rest=0\nfinal_body=head:"
       << observation.final_head.value()
       << ",continuation:" << observation.final_continuation.value()
       << ",morphology:"
       << handoff.standing.standing.standing.body.regions[0].morphology
       << ",mathematical:"
       << handoff.standing.standing.standing.mathematical_morphology
       << ",codec:" << handoff.standing.standing.standing.codec_morphology
       << ",characteristic:" << handoff.characteristic_morphology
       << ",trace_organ:" << handoff.trace_organ_morphology
       << "\nchecker_exit=" << observation.passage.raw.exit_status
       << "\nformal_begin\n";
  deed.write(observation.passage.formal.bytes,
             observation.passage.formal.byte_count);
  deed << "formal_end\nphysical_telemetry=engine_time:unknown,checker_time:"
          "unknown,energy:unknown\n";
  return failed == 0 ? 0 : 1;
}
