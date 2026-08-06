#include <fstream>

#include <holonics/apparatus/cultivated_organ_executor.hpp>
#include <holonics/apparatus/cultivated_organ_store_adapter.hpp>
#include <holonics/apparatus/rederivation_store_adapter.hpp>

namespace {
std::size_t failures(const holonics::apparatus::cultivated_executor_receipt &e,
    const holonics::event::cultivation_observation &o,
    const holonics::event::cultivated_organ_rest_record &rest) {
  using holonics::organ::cultivation_obstruction;
  constexpr std::int64_t expected[4][6]{{1,1,-2,-1,0,0},{1,4,4,-4,-8,-4},
      {5,-2,1,0,0,0},{1,-3,3,-1,0,0}};
  constexpr std::uint8_t order[4]{1,1,2,3}, degree[4]{1,2,0,0}, features[4]{4,6,3,4};
  std::size_t f = 0; auto check = [&f](bool failed) { f += failed; };
  check(!e.returned()); check(!o.inquiry.theory_formed);
  check(!o.inquiry.development_ports_distinct); check(!o.inquiry.all_candidates_exact);
  check(o.inquiry.atlas_rows != 38);
  check(o.inquiry.controls.constant_stream != cultivation_obstruction::nonunique_kernel);
  check(o.inquiry.controls.short_stream != cultivation_obstruction::insufficient_rows);
  check(o.passage.typed.state != holonics::event::checker_return_status::accepted);
  check(!o.rest.returned); check(!o.rest.samples_absent); check(!o.remount.organs_preserved);
  check(!o.handoff.returned); check(!o.final_can_continue);
  check(o.final_head.value() != 14'001'038); check(o.final_continuation.value() != 15'001'038);
  check(rest.applied); check(rest.integrity != holonics::event::cultivated_organ_rest_integrity(rest));
  for (std::uint8_t family = 0; family < 4; ++family) {
    const auto &organ = rest.organs[family];
    f += organ.identity.value() != 198'300U + family || !organ.checker_founded ||
        organ.order != order[family] || organ.degree != degree[family] ||
        organ.features != features[family] || !organ.primitive ||
        o.inquiry.families[family].candidate_count != 9;
    for (std::uint8_t i = 0; i < features[family]; ++i) f += organ.coefficients[i] != expected[family][i];
  }
  return f;
}
void atlas(std::ostream &out, const holonics::event::cultivation_observation &o) {
  out << "family\tcandidate\torder\tdegree\tfeatures\trows\trank\tnullity\tobstruction\tselected\tcoefficients\n";
  for (std::uint8_t family = 0; family < 4; ++family)
    for (std::uint8_t i = 0; i < 9; ++i) {
      const auto &x = o.inquiry.families[family].candidates[i];
      out << static_cast<unsigned>(family) << '\t' << static_cast<unsigned>(i) << '\t'
          << static_cast<unsigned>(x.order) << '\t' << static_cast<unsigned>(x.degree) << '\t'
          << static_cast<unsigned>(x.features) << '\t' << static_cast<unsigned>(x.rows) << '\t'
          << static_cast<unsigned>(x.rank) << '\t' << static_cast<unsigned>(x.nullity) << '\t'
          << static_cast<unsigned>(x.obstruction) << '\t' << x.selected << '\t';
      for (std::uint8_t k = 0; k < x.features; ++k) out << (k ? "," : "") << x.coefficients[k];
      out << '\n';
    }
  out << "control\tconstant\t-\t-\t-\t-\t-\t-\t"
      << static_cast<unsigned>(o.inquiry.controls.constant_stream) << "\t0\t-\n"
      << "control\tshort\t-\t-\t-\t-\t-\t-\t"
      << static_cast<unsigned>(o.inquiry.controls.short_stream) << "\t0\t-\n";
}
}  // namespace

int main(int argc, char **argv) {
  if (argc != 17) return 2;
  holonics::apparatus::cultivation_mount mount{};
  const auto rest_load = holonics::apparatus::read_rederivation_handoff(argv[2], mount.inherited);
  holonics::apparatus::cultivated_store_receipt cards[4]{}; bool loaded = rest_load.returned();
  for (std::uint8_t i = 0; i < 4; ++i) {
    cards[i] = holonics::apparatus::read_developmental_stream_card(argv[4+i], mount.cards[i]);
    loaded = loaded && cards[i].returned();
  }
  if (!loaded) return 3;
  const holonics::apparatus::lean_process_configuration process{
      argv[12],argv[13],argv[14],argv[8],argv[9],argv[10],argv[11],argv[15]};
  holonics::event::cultivation_observation observation{};
  holonics::organ::cultivation_workspace workspace{};
  holonics::event::cultivated_organ_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_organ_cultivation(
      mount, process, observation, workspace, handoff);
  const auto rest_write = holonics::apparatus::write_cultivated_organ_rest(argv[3], handoff);
  const auto failed = failures(execution, observation, handoff) + !rest_write.returned();
  std::ofstream deed{argv[1], std::ios::binary|std::ios::trunc},
      atlas_file{argv[16], std::ios::binary|std::ios::trunc};
  if (!deed || !atlas_file) return 4;
  deed << "truth_status=established-bounded\nevidence=implemented-exact,computational-witness\n"
      << "formal_truth_status=proved-derived\nformal_evidence=formal-checked\n"
      << "program=r31_organ_cultivation.sm_" << execution.device_major << execution.device_minor
      << "\nverification_failures=" << failed << "\nkernel_launches=" << execution.kernel_launches.value()
      << "\nsource_currents=" << execution.source_currents.value() << "\nhost_semantic_events=0\n"
      << "candidate_atlas_rows=" << observation.inquiry.atlas_rows
      << "\nintermediate_rest_bytes=" << sizeof(handoff) << "\nsamples_in_rest=0\n"
      << "final_body=head:" << observation.final_head.value() << ",continuation:"
      << observation.final_continuation.value() << ",morphology:" << handoff.standing.body.regions[0].morphology
      << ",mathematical:" << handoff.standing.mathematical_admitted_tally << ",codec:"
      << handoff.standing.codec_admitted_tally << ",organ:" << handoff.organ_admitted_tally
      << "\nchecker_exit=" << observation.passage.raw.exit_status << "\nformal_begin\n";
  deed.write(observation.passage.formal.bytes, observation.passage.formal.byte_count);
  deed << "formal_end\nphysical_telemetry=engine_time:unknown,checker_time:unknown,energy:unknown\n";
  atlas(atlas_file, observation); return failed == 0 ? 0 : 1;
}
