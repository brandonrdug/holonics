#include "r25_artifact.hpp"

#include <ostream>

namespace holonics::tests {
namespace {

void polynomial(std::ostream& output,
    const organ::causal_characteristic_receipt& value) {
  for (std::uint8_t slot = 0; slot <= value.degree; ++slot) {
    if (slot != 0) { output << ','; }
    output << value.coefficients[slot];
  }
}

void matrix_two(std::ostream& output, const std::int64_t value[2][2]) {
  output << value[0][0] << ',' << value[0][1] << ';'
      << value[1][0] << ',' << value[1][1];
}

}  // namespace

void write_r25_artifact(std::ostream& output, bool sources_loaded,
    const apparatus::causal_linear_store_receipt& card_load,
    const apparatus::causal_linear_store_receipt& rest_load,
    const apparatus::causal_linear_store_receipt& rest_write,
    const apparatus::causal_linear_executor_receipt& execution,
    const apparatus::causal_linear_probe_receipt& probe,
    const organ::causal_linear_receipt& changed,
    const event::causal_linear_observation& value,
    const event::causal_linear_rest_record& handoff,
    std::size_t failures) noexcept {
  const auto& inquiry = value.inquiry;
  output << "truth_status=established-bounded\n"
      << "evidence=implemented-exact,computational-witness\n"
      << "formal_truth_status=proved-derived\nformal_evidence=formal-checked\n"
      << "hodge_conjecture_status=outside-aperture\n"
      << "riemann_hypothesis_status=outside-aperture\n"
      << "program=r25_causal_linear_chain_calculus.sm_89\n"
      << "device_compute_capability=" << execution.device_major << '.' << execution.device_minor
      << "\nkernel_launches=" << execution.kernel_launches.value()
      << "\nlaunched_threads=" << execution.launched_threads.value()
      << "\nsemantic_threads=" << execution.semantic_threads.value()
      << "\nbytes_to_device=" << execution.bytes_to_device.value()
      << "\nbytes_from_device=" << execution.bytes_from_device.value()
      << "\nresident_bytes=" << execution.resident_bytes.value()
      << "\nhost_semantic_events=" << execution.host_semantic_events.value()
      << "\nverification_failures=" << failures
      << "\nexecutor_state=" << static_cast<unsigned>(execution.state)
      << "\nprobe_state=" << static_cast<unsigned>(probe.state)
      << "\npredecessor_remount=body:" << value.predecessor_remount.body.returned
      << ",same_body:" << value.predecessor_remount.same_body
      << ",theory:" << value.predecessor_remount.theory_preserved
      << ",source_replayed:" << value.predecessor_remount.source_replayed
      << ",theory_id:" << value.predecessor_remount.theory.value()
      << "\nformation_state=" << static_cast<unsigned>(value.passage.formation_commit.state)
      << ",checker_stage:" << static_cast<unsigned>(value.passage.checker_stage)
      << ",formal_bytes:" << value.passage.formal.byte_count
      << "\ninquiry_state=all_exact:" << value.inquiry.all_exact
      << ",theory_formed:" << value.inquiry.theory_formed
      << ",source_mask:" << +value.inquiry.source_mask
      << ",obstruction:" << static_cast<unsigned>(value.inquiry.obstruction)
      << ",phase_exact:" << value.inquiry.phase.exact
      << ",phase_d1:" << value.inquiry.phase.boundary_one_analysis.exact
      << ",phase_d2:" << value.inquiry.phase.boundary_two_analysis.exact
      << ",phase_char:" << value.inquiry.phase.diagonal_characteristic.exact
      << ",cm_exact:" << value.inquiry.cm.exact
      << ",cm_incidence:" << value.inquiry.cm.incidence_analysis.exact
      << ",cm_char:" << value.inquiry.cm.adjacency_characteristic.exact
      << ",cm_agrees:" << value.inquiry.cm.domain_characteristic_agrees
      << ",cm_factor:" << value.inquiry.cm.factor_exact
      << ",toric_exact:" << value.inquiry.toric.exact
      << ",variation_exact:" << value.inquiry.variation.exact
      << "\nsource_cards=all_loaded:" << sources_loaded << ",r25_bytes:"
      << card_load.bytes.value() << ",fold:" << card_load.byte_fold
      << ",path_fold:" << card_load.path_fold
      << "\nsource_aperture=phase_product:2x3,cm_periodic:16x40,toric_fans:3+4,"
         "variation:pencil+form+loops,expected_invariants:absent"
      << "\npredecessor=rest_bytes:" << rest_load.bytes.value() << ",head:14001022"
      << "\nphase=cells:" << +inquiry.phase.vertices << ',' << +inquiry.phase.edges << ','
      << +inquiry.phase.faces << ",ranks:" << +inquiry.phase.boundary_one_analysis.rank << ','
      << +inquiry.phase.boundary_two_analysis.rank << ",betti:" << +inquiry.phase.betti[0]
      << ',' << +inquiry.phase.betti[1] << ',' << +inquiry.phase.betti[2]
      << ",tours:" << +inquiry.phase.tours << 'x' << +inquiry.phase.tour_length
      << ",boundary_squared_zero:" << inquiry.phase.boundary_composite_zero
      << "\ncm=incidence_rank:" << +inquiry.cm.incidence_analysis.rank << ",homology:"
      << +inquiry.cm.homology_zero << ',' << +inquiry.cm.homology_one
      << ",characteristic:";
  polynomial(output, inquiry.cm.adjacency_characteristic);
  output << ",factors:";
  for (std::uint8_t factor = 0; factor < inquiry.cm.factor_count; ++factor) {
    if (factor != 0) { output << ';'; }
    output << inquiry.cm.factor_roots[factor] << '^'
        << +inquiry.cm.factor_multiplicities[factor];
  }
  output << "\ntoric=free_cokernel:" << +inquiry.toric.source[0].free_cokernel_rank << ','
      << +inquiry.toric.source[1].free_cokernel_rank << ','
      << +inquiry.toric.blowup.free_cokernel_rank << ",smith:"
      << inquiry.toric.source[0].smith[0] << ',' << inquiry.toric.source[0].smith[1]
      << ';' << inquiry.toric.source[1].smith[0] << ',' << inquiry.toric.source[1].smith[1]
      << ';' << inquiry.toric.blowup.smith[0] << ',' << inquiry.toric.blowup.smith[1]
      << ",exceptional_square:" << inquiry.toric.exceptional_square
      << "\nvariation=pencil:";
  for (std::uint8_t row = 0; row < 2; ++row) {
    if (row != 0) { output << ';'; }
    for (std::uint8_t column = 0; column < 2; ++column) {
      if (column != 0) { output << ','; }
      output << inquiry.variation.pencil[row][column][0] << '+'
          << inquiry.variation.pencil[row][column][1] << 't';
    }
  }
  output << ",determinant:" << inquiry.variation.determinant[0] << ','
      << inquiry.variation.determinant[1] << ',' << inquiry.variation.determinant[2]
      << ",ranks:" << +inquiry.variation.ranks[0] << ',' << +inquiry.variation.ranks[1]
      << ',' << +inquiry.variation.ranks[2] << ",form:";
  matrix_two(output, inquiry.variation.form);
  output << "\ncontrols=equal_characteristic_unequal_fixed:"
      << inquiry.controls.equal_characteristic_unequal_fixed << ",fixed:"
      << +inquiry.controls.identity_fixed << ',' << +inquiry.controls.jordan_fixed
      << ",unequal_kernel_placement:" << inquiry.controls.unequal_kernel_placement
      << ",rational_rotation_eigenvalue_absent:"
      << inquiry.controls.rational_eigenvalue_absent << ",rational_discriminant:"
      << inquiry.controls.rational_discriminant << ",gaussian_eigenpair:"
      << inquiry.controls.gaussian_eigenpair_exact
      << "\nprobe=returned:" << probe.returned() << ",phase:"
      << +changed.phase.vertices << ',' << +changed.phase.edges << ','
      << +changed.phase.faces << ",ranks:" << +changed.phase.boundary_one_analysis.rank << ','
      << +changed.phase.boundary_two_analysis.rank << ",tours:"
      << +changed.phase.tours << 'x' << +changed.phase.tour_length
      << ",all_exact:" << changed.all_exact << ",source_mask:" << +changed.source_mask
      << ",phase_exact:" << changed.phase.exact << ",cm_exact:" << changed.cm.exact
      << "\nchecker=exit:" << value.passage.raw.exit_status << ",stdout_bytes:"
      << value.passage.raw.stdout_bytes << ",stderr_bytes:" << value.passage.raw.stderr_bytes
      << ",produced_bytes:" << value.passage.raw.produced_artifact_bytes
      << "\nfinal_body=head:" << handoff.body.head << ",continuation:"
      << handoff.body.continuation << ",morphology:" << handoff.body.regions[0].morphology
      << ",mathematical:" << handoff.mathematical_admitted_tally << ",codec:"
      << handoff.codec_admitted_tally << ",causal_linear:" << handoff.causal_linear_admitted_tally
      << ",rest_bytes:" << rest_write.bytes.value() << ",integrity:" << handoff.integrity
      << "\nphysical_telemetry=engine_time:unknown,checker_time:unknown,temperature:unknown,"
         "power:unknown,energy:unknown\nformal_begin\n";
  output.write(value.passage.formal.bytes, value.passage.formal.byte_count);
  output << "formal_end\nconversation_begin\n";
  output.write(value.passage.conversational.bytes, value.passage.conversational.byte_count);
  output << "conversation_end\nchecker_stdout_begin\n";
  output.write(value.passage.raw.standard_output, value.passage.raw.stdout_bytes);
  output << "checker_stdout_end\n";
}

void write_r25_atlas(std::ostream& output,
    const organ::causal_linear_receipt& value) noexcept {
  output << "kind\towner\tshape\trank\tnullity\tidentity\tlineage\texact\n";
  output << "boundary\tphase_d1\t" << +value.phase.boundary_one.rows << 'x'
      << +value.phase.boundary_one.columns << '\t'
      << +value.phase.boundary_one_analysis.rank << '\t'
      << +value.phase.boundary_one_analysis.nullity << '\t'
      << value.phase.boundary_one.identity.value() << '\t'
      << value.phase.boundary_one.lineage.value() << '\t' << value.phase.exact << '\n';
  output << "boundary\tphase_d2\t" << +value.phase.boundary_two.rows << 'x'
      << +value.phase.boundary_two.columns << '\t'
      << +value.phase.boundary_two_analysis.rank << '\t'
      << +value.phase.boundary_two_analysis.nullity << '\t'
      << value.phase.boundary_two.identity.value() << '\t'
      << value.phase.boundary_two.lineage.value() << '\t' << value.phase.exact << '\n';
  output << "boundary\tcm_incidence\t" << +value.cm.incidence.rows << 'x'
      << +value.cm.incidence.columns << '\t' << +value.cm.incidence_analysis.rank << '\t'
      << +value.cm.incidence_analysis.nullity << '\t' << value.cm.incidence.identity.value()
      << '\t' << value.cm.incidence.lineage.value() << '\t' << value.cm.exact << '\n';
  for (std::uint8_t map = 0; map < 2; ++map) {
    output << "character_map\ttoric" << +map << '\t'
        << +value.toric.source[map].character.rows << 'x'
        << +value.toric.source[map].character.columns << '\t'
        << +value.toric.source[map].analysis.rank << '\t'
        << +value.toric.source[map].analysis.nullity << '\t'
        << value.toric.source[map].identity.value() << '\t'
        << value.toric.source[map].lineage.value() << '\t'
        << value.toric.source[map].exact << '\n';
  }
  output << "tensor\tvariation_loops\t" << +value.variation.tensor.rows << 'x'
      << +value.variation.tensor.columns << "\t4\t0\t"
      << value.variation.tensor.identity.value() << '\t'
      << value.variation.tensor.lineage.value() << '\t' << value.variation.exact << '\n';
}

}  // namespace holonics::tests
