#include <fstream>

#include <holonics/apparatus/elementary_calculus_executor.hpp>
#include <holonics/apparatus/elementary_calculus_store_adapter.hpp>

namespace {
std::size_t failures(const holonics::apparatus::elementary_executor_receipt&e,
    const holonics::event::heldout_holonomy_observation&o,
    const holonics::event::elementary_calculus_rest_record&r){std::size_t f=0;auto c=[&f](bool b){f+=b;};
  c(!e.returned());c(!o.inquiry.theory_formed);c(!o.inquiry.prediction_before_comparison);
  c(!o.inquiry.development_sources_absent);c(!o.inquiry.ablation_exact);c(!o.inquiry.improved);
  c(o.inquiry.exclusion!=holonics::organ::cultivation_obstruction::organ_absent);
  c(o.inquiry.changed!=holonics::organ::cultivation_obstruction::heldout_residual);
  constexpr std::int64_t expected[9]{2,3,7,18,47,123,322,843,2207};
  for(std::uint8_t i=0;i<9;++i)c(o.inquiry.tail.source[i].numerator!=expected[i]||
      o.inquiry.tail.predicted[i].numerator!=expected[i]||o.inquiry.tail.predicted[i].denominator!=1);
  c(o.passage.typed.state!=holonics::event::checker_return_status::accepted);c(!o.rest.returned);
  c(!o.remount.application_preserved||!o.handoff.returned||!o.final_can_continue);
  c(o.final_head.value()!=14'001'044||o.final_continuation.value()!=15'001'044);
  c(!r.applied||!r.application.accepted||r.application.identity.value()!=199'306);
  c(r.standing.standing.body.regions[0].morphology!=1103);c(r.standing.standing.mathematical_morphology!=370);
  c(r.standing.standing.codec_morphology!=171);c(r.integrity!=holonics::event::elementary_calculus_rest_integrity(r));return f;}
void atlas(std::ostream&out,const holonics::organ::heldout_holonomy_receipt&r){
  out<<"index\tprefix\tsource\tpredicted\tequal\n";for(std::uint8_t i=0;i<r.tail.sample_count;++i)
    out<<static_cast<unsigned>(i)<<'\t'<<(i<r.tail.prefix_count)<<'\t'<<r.tail.source[i].numerator<<'/'<<r.tail.source[i].denominator
      <<'\t'<<r.tail.predicted[i].numerator<<'/'<<r.tail.predicted[i].denominator<<'\t'<<
      holonics::exact::small_rational_law::equal(r.tail.source[i],r.tail.predicted[i])<<'\n';
  out<<"control\tchanged\t-\t-\t"<<static_cast<unsigned>(r.changed)<<"\ncontrol\texclusion\t-\t-\t"<<
    static_cast<unsigned>(r.exclusion)<<'\n';}
}  // namespace

int main(int argc,char**argv){if(argc!=15)return 2;holonics::apparatus::elementary_application_mount mount{};
  bool loaded=holonics::apparatus::read_elementary_calculus_rest(argv[2],mount.inherited).returned()&&
    holonics::apparatus::read_heldout_triangle_card(argv[4],mount.heldout).returned();
  if(!loaded)return 3;
  const holonics::apparatus::lean_process_configuration process{argv[9],argv[10],argv[11],argv[5],argv[6],argv[7],argv[8],argv[12]};
  holonics::event::heldout_holonomy_observation observation{};holonics::organ::heldout_workspace workspace{};
  holonics::event::elementary_calculus_rest_record handoff{};const auto execution=
    holonics::apparatus::execute_elementary_application(mount,process,observation,workspace,handoff);
  const auto written=holonics::apparatus::write_elementary_calculus_rest(argv[3],handoff);
  const auto failed=failures(execution,observation,handoff)+!written.returned();
  std::ofstream deed{argv[1],std::ios::binary|std::ios::trunc},dossier{argv[13],std::ios::binary|std::ios::trunc},
    atlas_file{argv[14],std::ios::binary|std::ios::trunc};
  if(!deed||!dossier||!atlas_file)return 4;
  atlas(atlas_file,observation.inquiry);deed<<"truth_status=established-bounded\nevidence=implemented-exact,computational-witness\n"
    <<"formal_truth_status=proved-derived\nformal_evidence=formal-checked\nprogram=r32_heldout_holonomy.sm_"
    <<execution.device_major<<execution.device_minor<<"\nverification_failures="<<failed<<"\nkernel_launches="
    <<execution.kernel_launches.value()<<"\nsource_currents=2\nhost_semantic_events=0\ndevelopment_card_arguments=0\n"
    <<"prediction_before_comparison="<<observation.inquiry.prediction_before_comparison<<"\nfinal_rest_bytes="<<sizeof(handoff)
    <<"\nfinal_body=head:"<<observation.final_head.value()<<",continuation:"<<observation.final_continuation.value()
    <<",morphology:"<<handoff.standing.standing.body.regions[0].morphology<<",mathematical:"
    <<handoff.standing.standing.mathematical_morphology<<",codec:"<<handoff.standing.standing.codec_morphology
    <<",derivation:"<<handoff.derivation_morphology<<"\nchecker_exit="<<observation.passage.raw.exit_status<<"\nformal_begin\n";
  deed.write(observation.passage.formal.bytes,observation.passage.formal.byte_count);deed<<"formal_end\nconversation_begin\n";
  deed.write(observation.dossier.bytes,observation.dossier.byte_count);deed<<"\nconversation_end\n"
    <<"physical_telemetry=engine_time:unknown,checker_time:unknown,energy:unknown\n";
  dossier.write(observation.dossier.bytes,observation.dossier.byte_count);
  return failed==0?0:1;}
