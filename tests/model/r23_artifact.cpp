#include "r23_artifact.hpp"

#include <ostream>

namespace holonics::tests {
namespace {
void rational(std::ostream& output, exact::small_rational value) {
  output << value.numerator;
  if (value.denominator != 1) { output << '/' << value.denominator; }
}

void vector(std::ostream& output, const exact::small_rational* values,
    std::uint8_t count) {
  for (std::uint8_t slot = 0; slot < count; ++slot) {
    if (slot != 0) { output << ','; }
    rational(output, values[slot]);
  }
}

void matrix(std::ostream& output,
    const exact::small_rational values[organ::toric_rank_capacity]
        [organ::toric_rank_capacity], std::uint8_t rank) {
  for (std::uint8_t row = 0; row < rank; ++row) {
    if (row != 0) { output << ';'; }
    vector(output, values[row], rank);
  }
}

}  // namespace

void write_r23_artifact(std::ostream& output,
    const apparatus::toric_store_receipt& card_load,
    const apparatus::toric_store_receipt& rest_load,
    const apparatus::toric_store_receipt& rest_write,
    const apparatus::toric_executor_receipt& execution,
    const apparatus::toric_probe_receipt& probe,
    const organ::toric_cycle_receipt& changed,
    const event::toric_cycle_observation& value,
    const event::toric_cycle_rest_record& handoff,
    std::size_t failures) noexcept {
  const auto& inquiry = value.inquiry;
  output << "truth_status=established-bounded\n"
      << "evidence=implemented-exact,computational-witness\n"
      << "standard_toric_status=proved-standard\n"
      << "formal_truth_status=proved-derived\n"
      << "formal_evidence=formal-checked\n"
      << "hodge_conjecture_status=outside-aperture\n"
      << "riemann_hypothesis_status=outside-aperture\n"
      << "program=r23_toric_cycle_class_blowup_transport.sm_89\n"
      << "device_compute_capability=" << execution.device_major << '.' << execution.device_minor
      << "\nkernel_launches=" << execution.kernel_launches.value()
      << "\nlaunched_threads=" << execution.launched_threads.value()
      << "\nsemantic_threads=" << execution.semantic_threads.value()
      << "\nbytes_to_device=" << execution.bytes_to_device.value()
      << "\nbytes_from_device=" << execution.bytes_from_device.value()
      << "\nresident_bytes=" << execution.resident_bytes.value()
      << "\nhost_semantic_events=" << execution.host_semantic_events.value()
      << "\nlogical_read_support=" << execution.logical.read_support.value()
      << "\nlogical_change_support=" << execution.logical.change_support.value()
      << "\nlogical_alternatives=" << execution.logical.alternatives_retained.value()
      << "\nlogical_obstructions=" << execution.logical.obstructions_retained.value()
      << "\nverification_failures=" << failures
      << "\nsource_card=bytes:" << card_load.bytes.value() << ",fold:" << card_load.byte_fold
      << ",path_fold:" << card_load.path_fold
      << "\nsource_aperture=fans:2,rays:3,4,selected_cone:0,representatives:-4:4,"
         "expected_names:absent"
      << "\npredecessor=rest_bytes:" << rest_load.bytes.value() << ",head:14001018"
      << "\nfan_3=primitive:" << inquiry.fans[0].primitive << ",smooth:"
      << inquiry.fans[0].smooth << ",complete:" << inquiry.fans[0].complete
      << ",smith:" << inquiry.fans[0].smith_invariants[0] << ','
      << inquiry.fans[0].smith_invariants[1] << ",picard_rank:"
      << +inquiry.quotients[0].rank << ",inertia:" << +inquiry.intersections[0].positive
      << ',' << +inquiry.intersections[0].negative << ','
      << +inquiry.intersections[0].radical << ",determinant:"
      << inquiry.intersections[0].determinant.numerator << ",betti_middle:"
      << +inquiry.comparisons[0].betti[2] << ",hodge_11:"
      << +inquiry.comparisons[0].hodge[1][1]
      << "\nfan_4=primitive:" << inquiry.fans[1].primitive << ",smooth:"
      << inquiry.fans[1].smooth << ",complete:" << inquiry.fans[1].complete
      << ",smith:" << inquiry.fans[1].smith_invariants[0] << ','
      << inquiry.fans[1].smith_invariants[1] << ",picard_rank:"
      << +inquiry.quotients[1].rank << ",inertia:" << +inquiry.intersections[1].positive
      << ',' << +inquiry.intersections[1].negative << ','
      << +inquiry.intersections[1].radical << ",determinant:"
      << inquiry.intersections[1].determinant.numerator << ",betti_middle:"
      << +inquiry.comparisons[1].betti[2] << ",hodge_11:"
      << +inquiry.comparisons[1].hodge[1][1] << "\nfan_4_form=";
  matrix(output, inquiry.intersections[1].quotient_form, inquiry.quotients[1].rank);
  output << "\nfan_4_congruence=";
  matrix(output, inquiry.intersections[1].congruence_form, inquiry.quotients[1].rank);
  output << ",basis_determinant:";
  rational(output, inquiry.intersections[1].basis_determinant);
  output << "\nfan_chow_agreement=" << inquiry.intersections[0].fan_chow_agree << ','
      << inquiry.intersections[1].fan_chow_agree
      << "\nfan_3_polarization=primitive:";
  vector(output, inquiry.source_polarization.primitive, inquiry.quotients[0].rank);
  output << ",positive:" << inquiry.source_polarization.response_positive
      << ",orthogonal_direction:" << inquiry.source_polarization.has_orthogonal_direction
      << "\nintegral_fiber=class:";
  vector(output, inquiry.realizations[0].class_coordinates, inquiry.quotients[1].rank);
  output << ",kernel_rank:" << +inquiry.realizations[0].kernel_rank
      << ",representatives:" << inquiry.realizations[0].representative_count
      << ",first_identity:" << inquiry.realizations[0].representatives[0].identity.value()
      << ",first_lineage:" << inquiry.realizations[0].representatives[0].lineage
      << "\nrational_fiber=class:";
  vector(output, inquiry.realizations[1].class_coordinates, inquiry.quotients[1].rank);
  output << ",representatives:" << inquiry.realizations[1].representative_count
      << ",integral:false\nincompatible_fiber=obstructed:"
      << (inquiry.realizations[2].state == organ::toric_realization_state::incompatible)
      << "\npolarization=primitive:";
  vector(output, inquiry.polarization.primitive, inquiry.quotients[1].rank);
  output << ",negative:";
  vector(output, inquiry.polarization.primitive_negative, inquiry.quotients[1].rank);
  output << ",negative_square:"; rational(output, inquiry.polarization.primitive_square);
  output << "\nblowup=ray:" << inquiry.blowup.derived_ray.x << ','
      << inquiry.blowup.derived_ray.y << ",exceptional:";
  vector(output, inquiry.blowup.exceptional, inquiry.blowup.quotient.rank);
  output << ",exceptional_square:"; rational(output, inquiry.blowup.exceptional_square);
  output << ",projection_formula:" << inquiry.blowup.projection_formula
      << ",pullback_kernel_image:" << +inquiry.blowup.pullback_kernel_rank << ','
      << +inquiry.blowup.pullback_image_rank << ",pushforward_kernel_image:"
      << +inquiry.blowup.pushforward_kernel_rank << ','
      << +inquiry.blowup.pushforward_image_rank << ",betti_middle:"
      << +inquiry.blowup.comparison.betti[2] << ",hodge_11:"
      << +inquiry.blowup.comparison.hodge[1][1]
      << ",negative:";
  vector(output, inquiry.blowup.polarization.primitive_negative,
      inquiry.blowup.quotient.rank);
  output << ",negative_square:";
  rational(output, inquiry.blowup.polarization.primitive_square);
  output << "\nfoils=nonprimitive:" << inquiry.foils.nonprimitive_rejected
      << ",nonsmooth:" << inquiry.foils.nonsmooth_rejected
      << ",incomplete:" << inquiry.foils.incomplete_rejected
      << ",false_integral:" << inquiry.foils.false_integral_lift_rejected
      << ",incompatible:" << inquiry.foils.incompatible_response_rejected
      << ",wrong_subdivision:" << inquiry.foils.wrong_subdivision_rejected
      << ",principal_not_zero_support:" << inquiry.foils.principal_not_zero_support
      << ",congruence_not_conjugacy:"
      << inquiry.foils.congruence_not_operator_conjugacy
      << ",equal_class_not_support:" << inquiry.foils.equal_class_not_equal_support
      << "\nprobe=returned:" << probe.returned() << ",changed_class:";
  vector(output, changed.realizations[0].class_coordinates, changed.quotients[1].rank);
  output << "\nchecker=exit:" << value.passage.raw.exit_status << ",stdout_bytes:"
      << value.passage.raw.stdout_bytes << ",stderr_bytes:" << value.passage.raw.stderr_bytes
      << ",produced_bytes:" << value.passage.raw.produced_artifact_bytes
      << ",source_fold:" << value.passage.raw.source_fold << ",artifact_fold:"
      << value.passage.raw.produced_artifact_fold
      << "\nfinal_body=head:" << handoff.body.head << ",continuation:"
      << handoff.body.continuation
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

void write_r23_atlas(std::ostream& output,
    const organ::toric_cycle_receipt& value) noexcept {
  output << "kind\towner\tcoordinate\ttransport\tadmitted\tidentity\tlineage"
      "\tobstruction\texact\n";
  for (std::uint8_t fan = 0; fan < 2; ++fan) {
    for (std::uint8_t ray = 0; ray < value.fans[fan].source.ray_count; ++ray) {
      output << "ray\tfan" << +fan << "\t" << value.fans[fan].source.rays[ray].x
          << ',' << value.fans[fan].source.rays[ray].y << "\tclass=";
      vector(output, value.quotients[fan].divisor_classes[ray],
          value.quotients[fan].rank);
      output << "\t1\t" << value.fans[fan].identity.value() << '\t'
          << value.fans[fan].lineage << "\t0\t1\n";
    }
  }
  for (std::uint8_t target = 0; target < 3; ++target) {
    output << "inverse_fiber\ttarget" << +target << "\tclass=";
    vector(output, value.realizations[target].class_coordinates,
        value.quotients[1].rank);
    output << "\trepresentatives=" << value.realizations[target].representative_count
        << "\t" << (value.realizations[target].state !=
            organ::toric_realization_state::incompatible)
        << '\t' << value.realizations[target].identity.value() << '\t'
        << value.realizations[target].lineage << '\t'
        << (value.realizations[target].state ==
            organ::toric_realization_state::incompatible ? "incompatible" : "0")
        << "\t" << value.realizations[target].exact << '\n';
    for (std::uint16_t slot = 0;
        slot < value.realizations[target].representative_count; ++slot) {
      const auto& representative = value.realizations[target].representatives[slot];
      output << "representative\ttarget" << +target << "\tcoefficients=";
      vector(output, representative.coefficients, value.fans[1].source.ray_count);
      output << "\tsupport=" << +representative.support_mask << "\t1\t"
          << representative.identity.value() << '\t' << representative.lineage
          << "\t0\t1\n";
    }
  }
  for (std::uint8_t ray = 0; ray < value.blowup.old_ray_count; ++ray) {
    output << "transform\told_ray" << +ray << "\tstrict=";
    vector(output, value.blowup.transforms[ray].strict, value.blowup.quotient.rank);
    output << "\ttotal=";
    vector(output, value.blowup.transforms[ray].total, value.blowup.quotient.rank);
    output << "\t1\t" << value.blowup.transforms[ray].identity.value() << '\t'
        << value.blowup.transforms[ray].lineage << "\t0\t"
        << value.blowup.transforms[ray].exact << '\n';
  }
  output << "subdivision\tblowup\tray=" << value.blowup.derived_ray.x << ','
      << value.blowup.derived_ray.y << "\texceptional=";
  vector(output, value.blowup.exceptional, value.blowup.quotient.rank);
  output << ",square="; rational(output, value.blowup.exceptional_square);
  output << "\t1\t" << value.blowup.identity.value() << '\t' << value.blowup.lineage
      << "\t0\t" << value.blowup.exact << '\n';
  output << "foil\tprincipal_support\trelation=";
  for (std::uint8_t ray = 0; ray < value.fans[1].source.ray_count; ++ray) {
    if (ray != 0) { output << ','; }
    output << value.foils.retained_principal[ray];
  }
  output << "\tclass=0,support_nonzero=1\t0\t" << value.theory.statement.value()
      << '\t' << value.theory.lineage.value()
      << "\tprincipal_not_zero\t1\nfoil\tincompatible\tresidual=";
  vector(output, value.foils.retained_incompatible_residual,
      value.fans[1].source.ray_count);
  output << "\timage_membership=0\t0\t" << value.realizations[2].identity.value()
      << '\t' << value.realizations[2].lineage
      << "\tincompatible\t1\nfoil\twrong_subdivision\tray="
      << value.foils.retained_wrong_ray.x << ','
      << value.foils.retained_wrong_ray.y
      << "\tchain_map=0\t0\t" << value.blowup.identity.value() << '\t'
      << value.blowup.lineage << "\twrong_ray\t1\n";
}

}  // namespace holonics::tests
