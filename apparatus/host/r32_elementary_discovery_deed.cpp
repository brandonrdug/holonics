#include <fstream>

#include <holonics/apparatus/cultivated_organ_store_adapter.hpp>
#include <holonics/apparatus/elementary_calculus_executor.hpp>
#include <holonics/apparatus/elementary_calculus_store_adapter.hpp>

namespace {
std::size_t failures(const holonics::apparatus::elementary_executor_receipt&e,
    const holonics::event::elementary_calculus_observation&o,
    const holonics::event::elementary_calculus_rest_record&r){
  std::size_t f=0;auto check=[&f](bool bad){f+=bad;};check(!e.returned());check(!o.inquiry.theory_formed);
  check(!o.inquiry.development_ports_distinct);check(!o.inquiry.connected);
  check(o.inquiry.occurrence.selected_mask!=31);check(!o.inquiry.occurrence.boundary_squared_zero);
  check(!o.inquiry.composition.pairwise_distinct);
  check(!o.inquiry.receiver.first_factors_coarse);check(o.inquiry.receiver.strict_factors_coarse);
  check(!o.inquiry.receiver.strict_factors_fine);check(!o.inquiry.chart.curved);check(o.inquiry.chart.trace!=3);
  check(!o.inquiry.conduct.unique_least);check(o.inquiry.conduct.selected_population!=7);
  check(!o.inquiry.self_organ.selected_exact);check(o.inquiry.self_organ.organ.coefficients[0]!=1||
      o.inquiry.self_organ.organ.coefficients[1]!=-3||o.inquiry.self_organ.organ.coefficients[2]!=1);
  check(o.passage.typed.state!=holonics::event::checker_return_status::accepted);
  check(!o.rest.returned||!o.rest.development_rows_absent||!o.rest.traces_absent);
  check(!o.remount.laws_preserved||!o.handoff.returned||!o.final_can_continue);
  check(o.final_head.value()!=14'001'042||o.final_continuation.value()!=15'001'042);
  check(r.applied);check(r.integrity!=holonics::event::elementary_calculus_rest_integrity(r));
  check(r.laws.self_organ.identity.value()!=199'305||!r.laws.self_organ.checker_founded);
  for(std::uint8_t i=0;i<6;++i)check(r.laws.fibers[i].identity.value()!=199'300U+i||!r.laws.fibers[i].accepted);
  return f;
}
void identity_atlas(std::ostream&out,const holonics::organ::occurrence_incidence_receipt&r){
  out<<"kind\tcandidate\tpopulation\tcollisions\tobstruction\tselected\tresidual\n";
  for(const auto&x:r.masks)out<<"identity\t"<<static_cast<unsigned>(x.mask)<<'\t'<<
    static_cast<unsigned>(x.fields)<<'\t'<<static_cast<unsigned>(x.collisions)<<'\t'<<
    static_cast<unsigned>(x.obstruction)<<'\t'<<x.selected<<"\t-\n";
  for(const auto&x:r.boundaries){out<<"boundary\t"<<static_cast<unsigned>(x.candidate)<<"\t-\t-\t"<<
    static_cast<unsigned>(x.obstruction)<<'\t'<<x.selected<<'\t';
    for(const auto&row:x.residual) for(const auto value:row) out<<value<<',';
    out<<'\n';}
}
void composition_atlas(std::ostream&out,const holonics::organ::composition_receipt&r){
  out<<"case\tcode\tvisible\tcontact\tpredecessor\tforward\treverse\tequal\tobstruction\tresidual\n";
  for(std::uint8_t i=0;i<5;++i){const auto&x=r.signatures[i];out<<static_cast<unsigned>(i)<<'\t'<<
    static_cast<unsigned>(x.code)<<'\t'<<static_cast<unsigned>(x.visible)<<'\t'<<x.contact<<'\t'<<
    x.predecessor_link<<'\t'<<x.forward_complete<<'\t'<<x.reverse_complete<<'\t'<<x.complete_equal<<'\t'<<
    x.obstruction_present<<'\t';
    for(const auto value:x.residual)out<<value<<',';
    out<<'\n';}
}
void receiver_atlas(std::ostream&out,const holonics::organ::receiver_receipt&r){
  out<<"left\tright\tcoarse\tfine\tfirst\tstrict\n";for(std::uint8_t i=0;i<r.pair_count;++i){const auto&x=r.pairs[i];
    out<<static_cast<unsigned>(x.left)<<'\t'<<static_cast<unsigned>(x.right)<<'\t'<<x.same_coarse<<'\t'<<
    x.same_fine<<'\t'<<x.same_first<<'\t'<<x.same_strict<<'\n';}
}
void matrix_row(std::ostream&out,const char*name,const holonics::organ::exact_matrix2&m){
  out<<name;
  for(const auto value:m.value)out<<'\t'<<value;
  out<<'\n';}
void chart_atlas(std::ostream&out,const holonics::organ::chart_receipt&r){
  out<<"face\ta\tb\tc\td\n";matrix_row(out,"AB",r.first_path);matrix_row(out,"BA",r.second_path);
  matrix_row(out,"residual",r.residual);matrix_row(out,"closed",r.closed_word);matrix_row(out,"flat",r.flat_word);
}
void conduct_atlas(std::ostream&out,const holonics::organ::conduct_receipt&r){
  out<<"code\tconditions\terrors\tselected\n";for(const auto&x:r.candidates)
    out<<x.code<<'\t'<<static_cast<unsigned>(x.conditions)<<'\t'<<static_cast<unsigned>(x.errors)<<'\t'<<x.selected<<'\n';
}
void law_atlas(std::ostream&out,const holonics::organ::elementary_calculus_receipt&r){
  out<<"law\tvalue\tobstruction\nidentity_mask\t"<<static_cast<unsigned>(r.occurrence.selected_mask)<<"\t0\n"
     <<"coarse_fibers\t"<<static_cast<unsigned>(r.receiver.coarse_fibers)<<"\t0\n"
     <<"fine_fibers\t"<<static_cast<unsigned>(r.receiver.fine_fibers)<<"\t0\n"
     <<"strict_witnesses\t"<<static_cast<unsigned>(r.receiver.coarse_strict_witnesses)<<"\t0\n"
     <<"closed_trace\t"<<r.chart.trace<<"\t0\n";
  for(std::uint8_t i=0;i<3;++i){const auto&x=r.self_organ.candidates[i];out<<"organ_candidate_"<<
    static_cast<unsigned>(i)<<'\t';
    for(std::uint8_t j=0;j<x.features;++j)out<<x.coefficients[j]<<',';
    out<<'\t'<<static_cast<unsigned>(x.obstruction)<<'\n';}
}
}  // namespace

int main(int argc,char**argv){if(argc!=23)return 2;holonics::apparatus::elementary_discovery_mount mount{};
  bool loaded=holonics::apparatus::read_cultivated_organ_rest(argv[2],mount.inherited).returned();
  loaded=loaded&&holonics::apparatus::read_occurrence_incidence_card(argv[4],mount.cards.occurrence).returned();
  loaded=loaded&&holonics::apparatus::read_composition_card(argv[5],mount.cards.composition).returned();
  loaded=loaded&&holonics::apparatus::read_receiver_card(argv[6],mount.cards.receiver).returned();
  loaded=loaded&&holonics::apparatus::read_local_chart_card(argv[7],mount.cards.chart).returned();
  loaded=loaded&&holonics::apparatus::read_return_conduct_card(argv[8],mount.cards.conduct).returned();
  if(!loaded)return 3;
  const holonics::apparatus::lean_process_configuration process{argv[13],argv[14],argv[15],argv[9],argv[10],argv[11],argv[12],argv[16]};
  holonics::event::elementary_calculus_observation observation{};holonics::organ::elementary_workspace workspace{};
  holonics::event::elementary_calculus_rest_record handoff{};const auto execution=
    holonics::apparatus::execute_elementary_discovery(mount,process,observation,workspace,handoff);
  const auto written=holonics::apparatus::write_elementary_calculus_rest(argv[3],handoff);
  const auto failed=failures(execution,observation,handoff)+!written.returned();
  std::ofstream deed{argv[1],std::ios::binary|std::ios::trunc},a0{argv[17]},a1{argv[18]},a2{argv[19]},a3{argv[20]},a4{argv[21]},a5{argv[22]};
  if(!deed||!a0||!a1||!a2||!a3||!a4||!a5)return 4;
  identity_atlas(a0,observation.inquiry.occurrence);
  composition_atlas(a1,observation.inquiry.composition);receiver_atlas(a2,observation.inquiry.receiver);
  chart_atlas(a3,observation.inquiry.chart);conduct_atlas(a4,observation.inquiry.conduct);law_atlas(a5,observation.inquiry);
  deed<<"truth_status=established-bounded\nevidence=implemented-exact,computational-witness\nformal_truth_status=proved-derived\n"
    <<"formal_evidence=formal-checked\nprogram=r32_elementary_discovery.sm_"<<execution.device_major<<execution.device_minor
    <<"\nverification_failures="<<failed<<"\nkernel_launches="<<execution.kernel_launches.value()<<"\nsource_currents=5\n"
    <<"host_semantic_events=0\nidentity_candidates=31\nconduct_candidates=2187\nintermediate_rest_bytes="<<sizeof(handoff)
    <<"\ndevelopment_rows_in_rest=0\ntraces_in_rest=0\nfinal_body=head:"<<observation.final_head.value()<<",continuation:"
    <<observation.final_continuation.value()
    <<"\nchecker_exit="<<observation.passage.raw.exit_status<<"\nformal_begin\n";
  deed.write(observation.passage.formal.bytes,observation.passage.formal.byte_count);
  deed<<"formal_end\nphysical_telemetry=engine_time:unknown,checker_time:unknown,energy:unknown\n";
  return failed==0?0:1;}
