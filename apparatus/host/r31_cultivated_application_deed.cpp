#include <fstream>

#include <holonics/apparatus/cultivated_organ_executor.hpp>
#include <holonics/apparatus/cultivated_organ_store_adapter.hpp>

namespace {
std::size_t failures(const holonics::apparatus::cultivated_executor_receipt &e,
    const holonics::event::cultivated_application_observation &o,
    const holonics::event::cultivated_organ_rest_record &rest) {
  using holonics::organ::cultivation_obstruction;
  std::size_t f = 0; auto check = [&f](bool failed) { f += failed; };
  check(!e.returned()); check(!o.inquiry.theory_formed); check(!o.inquiry.all_exact);
  check(!o.inquiry.structure_ports_distinct); check(!o.inquiry.development_sources_absent);
  check(!o.inquiry.identity_ablation_exact);
  check(o.passage.typed.state != holonics::event::checker_return_status::accepted);
  check(!o.rest.returned); check(!o.remount.organs_preserved);
  check(!o.remount.application_preserved); check(!o.handoff.returned);
  check(!o.final_can_continue); check(o.final_head.value() != 14'001'040);
  check(o.final_continuation.value() != 15'001'040); check(!rest.applied);
  check(!rest.application.accepted); check(rest.application.identity.value() != 198'304);
  check(rest.integrity != holonics::event::cultivated_organ_rest_integrity(rest));
  check(o.dossier.byte_count == 0);
  constexpr std::uint8_t counts[4]{10,9,9,9}, prefixes[4]{1,1,2,3};
  for (std::uint8_t family = 0; family < 4; ++family) {
    const auto &tail = o.inquiry.tails[family];
    f += !tail.exact || !tail.prediction_before_comparison || tail.sample_count != counts[family] ||
        tail.prefix_count != prefixes[family] ||
        tail.changed_source != cultivation_obstruction::heldout_residual ||
        tail.short_prefix != cultivation_obstruction::insufficient_prefix ||
        tail.exclusion != cultivation_obstruction::organ_absent;
  }
  return f;
}
void atlas(std::ostream &out, const holonics::event::cultivated_application_observation &o) {
  out << "family\tindex\tprefix\tsource\tpredicted\tcompared_equal\tchanged\tshort\texclusion\n";
  for (std::uint8_t family = 0; family < 4; ++family) {
    const auto &tail = o.inquiry.tails[family];
    for (std::uint8_t i = 0; i < tail.sample_count; ++i)
      out << static_cast<unsigned>(family) << '\t' << static_cast<unsigned>(i) << '\t'
          << (i < tail.prefix_count) << '\t' << tail.source[i].numerator << '/'
          << tail.source[i].denominator << '\t' << tail.predicted[i].numerator << '/'
          << tail.predicted[i].denominator << '\t'
          << holonics::exact::small_rational_law::equal(tail.source[i], tail.predicted[i]) << '\t'
          << static_cast<unsigned>(tail.changed_source) << '\t'
          << static_cast<unsigned>(tail.short_prefix) << '\t'
          << static_cast<unsigned>(tail.exclusion) << '\n';
  }
}
}  // namespace

int main(int argc, char **argv) {
  if (argc != 18) return 2;
  holonics::apparatus::cultivated_application_mount mount{};
  const auto rest_load = holonics::apparatus::read_cultivated_organ_rest(argv[2], mount.inherited);
  holonics::apparatus::cultivated_store_receipt cards[4]{
      holonics::apparatus::read_star_structure_card(argv[4], mount.structures.star),
      holonics::apparatus::read_walk_structure_card(argv[5], mount.structures.walk),
      holonics::apparatus::read_signed_carrier_card(argv[6], mount.structures.carrier),
      holonics::apparatus::read_graded_structure_card(argv[7], mount.structures.graded)};
  bool loaded = rest_load.returned(); for (const auto &card : cards) loaded = loaded && card.returned();
  if (!loaded) return 3;
  const holonics::apparatus::lean_process_configuration process{
      argv[12],argv[13],argv[14],argv[8],argv[9],argv[10],argv[11],argv[15]};
  holonics::event::cultivated_application_observation observation{};
  holonics::event::cultivated_organ_rest_record handoff{};
  const auto execution = holonics::apparatus::execute_cultivated_application(
      mount, process, observation, handoff);
  const auto rest_write = holonics::apparatus::write_cultivated_organ_rest(argv[3], handoff);
  const auto failed = failures(execution, observation, handoff) + !rest_write.returned();
  std::ofstream deed{argv[1],std::ios::binary|std::ios::trunc}, dossier{argv[16],std::ios::binary|std::ios::trunc},
      atlas_file{argv[17],std::ios::binary|std::ios::trunc};
  if (!deed || !dossier || !atlas_file) return 4;
  deed << "truth_status=established-bounded\nevidence=implemented-exact,computational-witness\n"
      << "formal_truth_status=proved-derived\nformal_evidence=formal-checked\n"
      << "program=r31_cultivated_application.sm_" << execution.device_major << execution.device_minor
      << "\nverification_failures=" << failed << "\nkernel_launches=" << execution.kernel_launches.value()
      << "\nsource_currents=" << execution.source_currents.value() << "\nhost_semantic_events=0\n"
      << "development_card_arguments=0\npredictions_before_comparison=1\n"
      << "final_body=head:" << observation.final_head.value() << ",continuation:"
      << observation.final_continuation.value()
      << "\nchecker_exit=" << observation.passage.raw.exit_status << "\nformal_begin\n";
  deed.write(observation.passage.formal.bytes, observation.passage.formal.byte_count);
  deed << "formal_end\nconversation_begin\n";
  deed.write(observation.dossier.bytes, observation.dossier.byte_count);
  deed << "\nconversation_end\nphysical_telemetry=engine_time:unknown,checker_time:unknown,energy:unknown\n";
  dossier.write(observation.dossier.bytes, observation.dossier.byte_count);
  atlas(atlas_file, observation); return failed == 0 ? 0 : 1;
}
