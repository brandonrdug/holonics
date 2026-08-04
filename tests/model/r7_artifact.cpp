#include "r7_artifact.hpp"

#include <cstddef>
#include <ostream>

namespace holonics::tests {

void write_r7_artifact(std::ostream& output,
    const apparatus::receiver_geometry_executor_receipt& execution,
    const apparatus::receiver_geometry_observation& observation,
    std::size_t failures) noexcept {
  const auto& value = observation.receiver;
  output << "truth_status=established-bounded\n"
         << "evidence=implemented-exact,computational-witness\n"
         << "program=r7_core_receiver_geometry.sm_89\n"
         << "device_compute_capability=" << execution.device_major << '.'
         << execution.device_minor << '\n'
         << "kernel_launches=" << execution.kernel_launches.value() << '\n'
         << "launched_threads=" << execution.launched_threads.value() << '\n'
         << "bytes_to_device=" << execution.bytes_to_device.value() << '\n'
         << "bytes_from_device=" << execution.bytes_from_device.value() << '\n'
         << "resident_bytes=" << execution.resident_bytes.value() << '\n'
         << "host_semantic_deeds=" << execution.host_semantic_deeds.value() << '\n'
         << "program_identity=" << value.program_identity.value() << '\n'
         << "current_predecessor=" << observation.current_predecessor.head.value() << '\n'
         << "current_successor=" << observation.current_successor.head.value() << '\n'
         << "current_returned=" << observation.current_returned << '\n'
         << "all_deeds_returned=" << value.all_deeds_returned << '\n'
         << "verification_failures=" << failures << '\n';
  const auto& swing = value.swing;
  output << "projective_swing=original:" << swing.original.first.value() << ':'
         << swing.original.second.value() << ",transformed:"
         << swing.transformed.first.value() << ':' << swing.transformed.second.value()
         << ",path=" << swing.path.value() << ",equal=" << swing.projectively_equal
         << ",frame_changed=" << swing.frame_changed
         << ",degenerate_open=" << swing.degenerate_open
         << ",non_field_open=" << swing.non_field_open
         << ",obstruction=" << static_cast<unsigned>(swing.obstruction) << '\n';
  const auto& same = value.sameness;
  output << "sameness=occurrence:" << same.occurrence_equal
         << ",diagram:" << same.marked_diagram_isomorphic
         << ",doctrine:" << same.doctrinal_equivalent
         << ",observation:" << same.observationally_equivalent
         << ",receiver_face:" << same.receiver_face_equal
         << ",presentation:" << same.presentation_equal
         << ",bytes:" << same.byte_equal << ",digest:" << same.digest_equal
         << ",face_counterexample=" << same.equal_face_distinct_occurrence
         << ",byte_counterexample=" << same.equal_bytes_distinct_soul
         << ",digest_collision=" << same.digest_collision_retained << '\n';
  const auto& projection = value.projection;
  output << "projection=faces:" << projection.faces[0].value() << ':'
         << projection.faces[1].value() << ",preimages:"
         << projection.preimage_supports[0].value() << ':'
         << projection.preimage_supports[1].value() << ",counts:"
         << projection.preimage_counts[0] << ':' << projection.preimage_counts[1]
         << ",source_incidence=" << projection.source_incidence_before.value() << ':'
         << projection.source_incidence_after.value()
         << ",created=" << projection.created_source_incidence.value()
         << ",unresolved=" << projection.unresolved_preimage
         << ",counterexample=" << projection.counterexample_receivers_differ << '\n';
  for (std::size_t receiver_slot = 0; receiver_slot < 2; ++receiver_slot) {
    output << "projection_preimage=" << receiver_slot;
    for (std::size_t source = 0; source < projection.preimage_counts[receiver_slot]; ++source) {
      output << ':' << projection.preimage_occurrences[receiver_slot][source].value();
    }
    output << '\n';
  }
  const auto& connection = value.connection;
  output << "connection=endpoints:" << connection.start_endpoint.value() << ':'
         << connection.end_endpoint.value() << ",fiber:"
         << connection.initial_fiber.value() << ':' << connection.transported_fiber.value()
         << ",holonomy=" << connection.finite_holonomy.negative << ':'
         << connection.finite_holonomy.magnitude.value()
         << ",curvature=" << connection.local_curvature.negative << ':'
         << connection.local_curvature.magnitude.value()
         << ",endpoint_equal=" << connection.endpoint_equal
         << ",curvature_certified=" << connection.curvature_certified
         << ",open_residual_holonomy=" << connection.open_path_residual_is_holonomy
         << ",global_open=" << connection.global_triviality_open << '\n';
  const auto& hyper = value.hypergeometric;
  output << "hypergeometric=parameters:" << hyper.parameters[0].value() << ':'
         << hyper.parameters[1].value() << ':' << hyper.parameters[2].value()
         << ",singular:" << hyper.singular_locus[0].value() << ':'
         << hyper.singular_locus[1].value() << ':' << hyper.singular_locus[2].value()
         << ",branch=" << hyper.branch.value() << ",path=" << hyper.path.value()
         << ",lineage=" << hyper.lineage.value() << ",terms=" << hyper.term_count
         << ",recurrence=" << hyper.recurrence_exact
         << ",confluent_distinct=" << hyper.confluent_distinct
         << ",generalized_distinct=" << hyper.generalized_distinct << '\n';
  for (std::size_t slot = 0; slot < hyper.term_count; ++slot) {
    output << "solution_term=" << slot << ",coefficient="
           << hyper.coefficients[slot].first.value() << ':'
           << hyper.coefficients[slot].second.value() << '\n';
  }
  output << "monodromy=" << hyper.monodromy[0].value() << ':'
         << hyper.monodromy[1].value() << ':' << hyper.monodromy[2].value() << ':'
         << hyper.monodromy[3].value() << '\n';
  const auto& carrier = value.carrier;
  output << "extended_carrier=carriers:" << carrier.carriers[0].value() << ':'
         << carrier.carriers[1].value() << ':' << carrier.carriers[2].value()
         << ",contacts:" << carrier.contacts[0].value() << ':'
         << carrier.contacts[1].value() << ",line_boundary="
         << carrier.line_boundary_count << ",sheet_boundary_squared="
         << carrier.sheet_boundary_squared_zero << ",higher_boundary_squared="
         << carrier.higher_boundary_squared_zero << ",contacts_typed="
         << carrier.contacts_typed << ",presentations_distinct="
         << carrier.presentations_distinct << ",braid_interchange="
         << carrier.braid_interchange_certified << ",literal_identity="
         << carrier.literal_physical_identity << '\n';
  output << "carrier_presentations=" << carrier.knot_embedding.value() << ':'
         << carrier.received_diagram.value() << ':' << carrier.braid_presentation.value()
         << ':' << carrier.higher_face.value() << '\n';
  output << "sheet_residuals=";
  for (std::size_t slot = 0; slot < 4; ++slot) {
    output << (slot == 0 ? "" : ":") << static_cast<int>(carrier.sheet_vertex_residuals[slot]);
  }
  output << "\nhigher_residuals=";
  for (std::size_t slot = 0; slot < receiver::cube_edge_capacity; ++slot) {
    output << (slot == 0 ? "" : ":") << static_cast<int>(carrier.higher_edge_residuals[slot]);
  }
  const auto& info = value.information;
  output << "\ninformation_geometry=interval:" << info.interval_negative << ':'
         << info.interval_magnitude.value() << ':' << info.interval_denominator.value()
         << ",metric=" << info.metric[0].first.value() << ':'
         << info.metric[0].second.value() << '|'
         << info.metric[1].first.value() << ':' << info.metric[1].second.value()
         << ",metric_declared=" << info.metric_declared
         << ",accessible=" << info.causal_accessible
         << ",clocks:" << info.receiver_clocks[0].first.value() << ':'
         << info.receiver_clocks[0].second.value() << '|'
         << info.receiver_clocks[1].first.value() << ':'
         << info.receiver_clocks[1].second.value()
         << ",clocks_distinct=" << info.receiver_clocks_distinct
         << ",current=" << info.current_before.value() << ':' << info.current_after.value()
         << ",phase=" << info.carried_phase.value()
         << ",stress=" << info.returned_stress.value()
         << ",support=" << info.first_support.value() << ':' << info.second_support.value()
         << ",repeated=" << info.repeated_support
         << ",complete_state=" << info.complete_state_recurrence
         << ",domain_relative=" << info.accelerometer_domain_relative << ':'
         << info.cycle_domain_relative << ",relativistic_fidelity="
         << info.general_relativistic_fidelity << ",missing="
         << info.missing_relativistic_obligations.value() << '\n';
}

}  // namespace holonics::tests
