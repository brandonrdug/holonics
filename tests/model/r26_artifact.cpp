#include "r26_artifact.hpp"

#include <ostream>

namespace holonics::tests {

void write_r26_artifact(std::ostream& output, bool sources_loaded,
    const apparatus::intrinsic_hypergeometry_store_receipt& card_load,
    const apparatus::intrinsic_hypergeometry_store_receipt& rest_load,
    const apparatus::intrinsic_hypergeometry_store_receipt& rest_write,
    const apparatus::intrinsic_hypergeometry_executor_receipt& execution,
    const event::intrinsic_hypergeometry_observation& value,
    const event::intrinsic_hypergeometry_rest_record& handoff,
    std::size_t failures) noexcept {
  const auto& inquiry = value.inquiry;
  output << "truth_status=established-bounded\n"
      << "evidence=implemented-exact,computational-witness\n"
      << "formal_truth_status=proved-derived\nformal_evidence=formal-checked\n"
      << "hodge_conjecture_status=outside-aperture\n"
      << "riemann_hypothesis_status=outside-aperture\n"
      << "program=r26_intrinsic_hypergeometry_archetype_distribution.sm_89\n"
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
      << "\npredecessor_remount=body:" << value.predecessor_remount.body.returned
      << ",same_body:" << value.predecessor_remount.same_body
      << ",theory:" << value.predecessor_remount.theory_preserved
      << ",source_replayed:" << value.predecessor_remount.source_replayed
      << ",theory_id:" << value.predecessor_remount.theory.value()
      << "\ninquiry=all_exact:" << inquiry.all_exact
      << ",theory_formed:" << inquiry.theory_formed
      << ",source_mask:" << inquiry.source_mask
      << ",obstruction:" << static_cast<unsigned>(inquiry.obstruction)
      << ",no_expected_invariants:" << inquiry.no_expected_invariants
      << "\nsource_cards=all_loaded:" << sources_loaded
      << ",r26_bytes:" << card_load.bytes.value() << ",fold:" << card_load.byte_fold
      << ",path_fold:" << card_load.path_fold
      << "\nsource_aperture=phase_cases:10,vertices_per_case:323,edges_per_case:646,"
         "faces_per_case:323,flags_per_case:2584,series_depth:20,section_ring:Z/65521Z,"
         "cm_squares:40,expected_invariants:absent"
      << "\npredecessor=rest_bytes:" << rest_load.bytes.value() << ",head:14001024"
      << "\nphase_cases=";
  for (std::uint8_t slot = 0; slot < organ::intrinsic_case_capacity; ++slot) {
    const auto& phase = inquiry.cases[slot]; if (slot != 0) { output << ';'; }
    output << phase.presentation.first << 'x' << phase.presentation.second
        << ":cells=" << phase.vertex_count << ',' << phase.edge_count << ',' << phase.face_count
        << ",flags=" << phase.flag_count << ",tours=" << +phase.tour_count << 'x' << phase.lcm
        << ",projection_fibers=" << phase.projection_fiber_count
        << ",word_fold=" << phase.tours[0].word_fold;
  }
  output << "\nlocal_section=series_terms:" << +inquiry.series.count
      << ",recurrence_exact:" << inquiry.series.recurrence_exact
      << ",form_preserved:" << inquiry.local_system.form_preserved
      << ",ordered_resolutions_unequal:" << inquiry.local_system.alternatives_unequal
      << ",commutator:" << inquiry.local_system.commutator[0][0] << ','
      << inquiry.local_system.commutator[0][1] << ';'
      << inquiry.local_system.commutator[1][0] << ','
      << inquiry.local_system.commutator[1][1]
      << "\nsupported_cycle=cm_squares:" << +inquiry.supported.square_count
      << ",cycle_characteristic:";
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    if (slot != 0) { output << ','; }
    output << inquiry.supported.phase_characteristic.coefficients[slot];
  }
  output << ",phase_boundary:" << inquiry.supported.phase_cycle_is_boundary
      << ",cm_no_two_cell:" << inquiry.supported.cm_cycle_has_no_two_cell
      << ",filled_extension_obstructed:" << inquiry.supported.filled_extension_obstructed
      << ",supported_loop:" << inquiry.supported.supported_loop_admitted
      << "\ncontrols=equal_hull_unequal_transport:"
      << inquiry.controls.equal_hull_unequal_transport
      << ",equal_local_population_unequal_order:"
      << inquiry.controls.equal_local_population_unequal_order
      << ",equal_spectrum_unequal_support:"
      << inquiry.controls.equal_spectrum_unequal_support
      << ",conjugate_rechart:" << inquiry.controls.conjugate_rechart
      << ",changed_source_sensitive:" << inquiry.controls.changed_source_sensitive
      << "\nchanged_case=" << value.changed_case.presentation.first << 'x'
      << value.changed_case.presentation.second << ",cells:" << value.changed_case.vertex_count
      << ',' << value.changed_case.edge_count << ',' << value.changed_case.face_count
      << ",flags:" << value.changed_case.flag_count << ",tours:"
      << +value.changed_case.tour_count << 'x' << value.changed_case.lcm
      << ",word_fold:" << value.changed_case.tours[0].word_fold
      << "\nchecker=exit:" << value.passage.raw.exit_status << ",stdout_bytes:"
      << value.passage.raw.stdout_bytes << ",stderr_bytes:" << value.passage.raw.stderr_bytes
      << ",produced_bytes:" << value.passage.raw.produced_artifact_bytes
      << "\nfinal_body=head:" << handoff.body.head << ",continuation:"
      << handoff.body.continuation << ",morphology:" << handoff.body.regions[0].morphology
      << ",mathematical:" << handoff.mathematical_admitted_tally << ",codec:"
      << handoff.codec_admitted_tally << ",intrinsic_hypergeometry:"
      << handoff.intrinsic_hypergeometry_admitted_tally << ",rest_bytes:"
      << rest_write.bytes.value() << ",integrity:" << handoff.integrity
      << "\nphysical_telemetry=engine_time:unknown,checker_time:unknown,temperature:unknown,"
         "power:unknown,energy:unknown\nformal_begin\n";
  output.write(value.passage.formal.bytes, value.passage.formal.byte_count);
  output << "formal_end\nconversation_begin\n";
  output.write(value.passage.conversational.bytes, value.passage.conversational.byte_count);
  output << "conversation_end\nchecker_stdout_begin\n";
  output.write(value.passage.raw.standard_output, value.passage.raw.stdout_bytes);
  output << "checker_stdout_end\n";
}

}  // namespace holonics::tests
