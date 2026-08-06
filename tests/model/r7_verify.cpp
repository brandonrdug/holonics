#include "r7_verify.hpp"

#include <cstddef>

namespace holonics::tests {
namespace {

bool equal(const receiver::word_pair& left, const receiver::word_pair& right) noexcept {
  return left.first == right.first && left.second == right.second;
}

bool equal(const current::weave_cell& left, const current::weave_cell& right) noexcept {
  return left.identity == right.identity && left.value == right.value &&
      left.admitted_tally == right.admitted_tally && left.current == right.current &&
      left.lineage == right.lineage && left.placement == right.placement &&
      left.aperture == right.aperture;
}

bool equal(const current::weave_snapshot& left,
    const current::weave_snapshot& right) noexcept {
  if (left.head != right.head || left.incidence != right.incidence ||
      left.lineage_order != right.lineage_order || left.obstruction != right.obstruction ||
      left.cell_count != right.cell_count || left.event_count != right.event_count ||
      left.logical.capacity != right.logical.capacity || left.logical.used != right.logical.used) {
    return false;
  }
  for (std::size_t slot = 0; slot < left.cell_count; ++slot) {
    if (!equal(left.cells[slot], right.cells[slot])) { return false; }
  }
  for (std::size_t slot = 0; slot < left.event_count; ++slot) {
    if (left.emitted[slot] != right.emitted[slot] ||
        left.logical.reservations[slot] != right.logical.reservations[slot]) {
      return false;
    }
  }
  return true;
}

std::size_t swing_failures(const receiver::projective_swing_receipt& left,
    const receiver::projective_swing_receipt& right) noexcept {
  std::size_t failures = 0;
  failures += !equal(left.original, right.original);
  failures += !equal(left.transformed, right.transformed);
  failures += left.path != right.path || left.obstruction != right.obstruction;
  failures += left.projectively_equal != right.projectively_equal;
  failures += left.frame_changed != right.frame_changed;
  failures += left.degenerate_open != right.degenerate_open;
  failures += left.non_field_open != right.non_field_open;
  failures += !left.projectively_equal || !left.frame_changed || !left.degenerate_open ||
      !left.non_field_open;
  return failures;
}

std::size_t sameness_failures(const receiver::sameness_receipt& left,
    const receiver::sameness_receipt& right) noexcept {
  std::size_t failures = 0;
  failures += left.occurrence_equal != right.occurrence_equal;
  failures += left.marked_diagram_isomorphic != right.marked_diagram_isomorphic;
  failures += left.doctrinal_equivalent != right.doctrinal_equivalent;
  failures += left.observationally_equivalent != right.observationally_equivalent;
  failures += left.receiver_face_equal != right.receiver_face_equal;
  failures += left.presentation_equal != right.presentation_equal;
  failures += left.byte_equal != right.byte_equal || left.digest_equal != right.digest_equal;
  failures += left.equal_face_distinct_occurrence != right.equal_face_distinct_occurrence;
  failures += left.equal_bytes_distinct_soul != right.equal_bytes_distinct_soul;
  failures += left.digest_collision_retained != right.digest_collision_retained;
  failures += left.byte_implies_digest != right.byte_implies_digest;
  failures += left.occurrence_equal || left.observationally_equivalent ||
      !left.marked_diagram_isomorphic || !left.receiver_face_equal ||
      !left.digest_collision_retained;
  return failures;
}

std::size_t projection_failures(const receiver::projection_receipt& left,
    const receiver::projection_receipt& right) noexcept {
  std::size_t failures = 0;
  for (std::size_t slot = 0; slot < 2; ++slot) {
    failures += left.faces[slot] != right.faces[slot];
    failures += left.preimage_supports[slot] != right.preimage_supports[slot];
    failures += left.preimage_counts[slot] != right.preimage_counts[slot];
    for (std::size_t source = 0; source < receiver::projection_source_capacity; ++source) {
      failures += left.preimage_occurrences[slot][source] !=
          right.preimage_occurrences[slot][source];
    }
  }
  failures += left.source_incidence_before != right.source_incidence_before;
  failures += left.source_incidence_after != right.source_incidence_after;
  failures += left.created_source_incidence != right.created_source_incidence;
  failures += left.lineage != right.lineage;
  failures += left.unresolved_preimage != right.unresolved_preimage;
  failures += left.counterexample_receivers_differ != right.counterexample_receivers_differ;
  failures += left.source_incidence_before != left.source_incidence_after ||
      left.created_source_incidence.value() != 0 || !left.unresolved_preimage ||
      !left.counterexample_receivers_differ;
  return failures;
}

std::size_t connection_failures(const receiver::connection_receipt& left,
    const receiver::connection_receipt& right) noexcept {
  std::size_t failures = 0;
  failures += left.start_endpoint != right.start_endpoint || left.end_endpoint != right.end_endpoint;
  failures += left.initial_fiber != right.initial_fiber ||
      left.transported_fiber != right.transported_fiber;
  failures += left.finite_holonomy.magnitude != right.finite_holonomy.magnitude ||
      left.finite_holonomy.negative != right.finite_holonomy.negative;
  failures += left.local_curvature.magnitude != right.local_curvature.magnitude ||
      left.local_curvature.negative != right.local_curvature.negative;
  failures += left.lineage != right.lineage || left.endpoint_equal != right.endpoint_equal;
  failures += left.curvature_certified != right.curvature_certified;
  failures += left.open_path_residual_is_holonomy != right.open_path_residual_is_holonomy;
  failures += left.global_triviality_open != right.global_triviality_open;
  failures += !left.endpoint_equal || !left.curvature_certified ||
      left.open_path_residual_is_holonomy || !left.global_triviality_open;
  return failures;
}

std::size_t hypergeometric_failures(const receiver::hypergeometric_receipt& left,
    const receiver::hypergeometric_receipt& right) noexcept {
  std::size_t failures = 0;
  for (std::size_t slot = 0; slot < 3; ++slot) {
    failures += left.parameters[slot] != right.parameters[slot];
    failures += left.singular_locus[slot] != right.singular_locus[slot];
  }
  for (std::size_t slot = 0; slot < receiver::hypergeometric_term_capacity; ++slot) {
    failures += !equal(left.coefficients[slot], right.coefficients[slot]);
    failures += left.monodromy[slot] != right.monodromy[slot];
  }
  failures += left.branch != right.branch || left.path != right.path || left.lineage != right.lineage;
  failures += left.family != right.family || left.term_count != right.term_count;
  failures += left.recurrence_exact != right.recurrence_exact;
  failures += left.singular_locus_retained != right.singular_locus_retained;
  failures += left.branch_retained != right.branch_retained;
  failures += left.confluent_distinct != right.confluent_distinct;
  failures += left.generalized_distinct != right.generalized_distinct;
  failures += !left.recurrence_exact || !left.singular_locus_retained ||
      !left.branch_retained || !left.confluent_distinct || !left.generalized_distinct;
  return failures;
}

std::size_t carrier_failures(const receiver::extended_carrier_receipt& left,
    const receiver::extended_carrier_receipt& right) noexcept {
  std::size_t failures = 0;
  for (std::size_t slot = 0; slot < 3; ++slot) { failures += left.carriers[slot] != right.carriers[slot]; }
  for (std::size_t slot = 0; slot < 2; ++slot) { failures += left.contacts[slot] != right.contacts[slot]; }
  failures += left.knot_embedding != right.knot_embedding ||
      left.received_diagram != right.received_diagram ||
      left.braid_presentation != right.braid_presentation || left.higher_face != right.higher_face;
  for (std::size_t slot = 0; slot < 4; ++slot) {
    failures += left.sheet_vertex_residuals[slot] != right.sheet_vertex_residuals[slot];
  }
  for (std::size_t slot = 0; slot < receiver::cube_edge_capacity; ++slot) {
    failures += left.higher_edge_residuals[slot] != right.higher_edge_residuals[slot];
  }
  failures += left.line_boundary_count != right.line_boundary_count;
  failures += left.sheet_boundary_squared_zero != right.sheet_boundary_squared_zero;
  failures += left.higher_boundary_squared_zero != right.higher_boundary_squared_zero;
  failures += left.contacts_typed != right.contacts_typed;
  failures += left.presentations_distinct != right.presentations_distinct;
  failures += left.braid_interchange_certified != right.braid_interchange_certified;
  failures += left.literal_physical_identity != right.literal_physical_identity;
  failures += !left.sheet_boundary_squared_zero || !left.higher_boundary_squared_zero ||
      !left.contacts_typed || !left.presentations_distinct ||
      !left.braid_interchange_certified || left.literal_physical_identity;
  return failures;
}

std::size_t information_failures(const receiver::information_geometry_receipt& left,
    const receiver::information_geometry_receipt& right) noexcept {
  std::size_t failures = 0;
  failures += left.interval_magnitude != right.interval_magnitude;
  failures += left.interval_denominator != right.interval_denominator;
  for (std::size_t slot = 0; slot < 2; ++slot) {
    failures += !equal(left.metric[slot], right.metric[slot]);
    failures += !equal(left.receiver_clocks[slot], right.receiver_clocks[slot]);
  }
  failures += left.current_before != right.current_before || left.current_after != right.current_after;
  failures += left.carried_phase != right.carried_phase || left.returned_stress != right.returned_stress;
  failures += left.first_support != right.first_support || left.second_support != right.second_support;
  failures += left.standing_head != right.standing_head;
  failures += left.missing_relativistic_obligations != right.missing_relativistic_obligations;
  failures += left.interval_negative != right.interval_negative ||
      left.causal_accessible != right.causal_accessible ||
      left.metric_declared != right.metric_declared ||
      left.receiver_clocks_distinct != right.receiver_clocks_distinct ||
      left.connection_declared != right.connection_declared ||
      left.repeated_support != right.repeated_support ||
      left.complete_state_recurrence != right.complete_state_recurrence ||
      left.accelerometer_domain_relative != right.accelerometer_domain_relative ||
      left.cycle_domain_relative != right.cycle_domain_relative ||
      left.general_relativistic_fidelity != right.general_relativistic_fidelity;
  failures += left.interval_negative || !left.causal_accessible || !left.metric_declared ||
      !left.receiver_clocks_distinct ||
      !left.connection_declared || !left.repeated_support || left.complete_state_recurrence ||
      !left.accelerometer_domain_relative || !left.cycle_domain_relative ||
      left.general_relativistic_fidelity || left.missing_relativistic_obligations.value() == 0;
  return failures;
}

}  // namespace

std::size_t r7_verification_failures(
    const apparatus::receiver_geometry_executor_receipt& execution,
    const apparatus::receiver_geometry_observation& actual,
    const apparatus::receiver_geometry_observation& oracle) noexcept {
  std::size_t failures = 0;
  failures += !execution.returned();
  failures += execution.kernel_launches != exact::word{3};
  failures += execution.host_semantic_deeds != exact::word{0};
  failures += actual.current_returned != oracle.current_returned || !actual.current_returned;
  failures += !equal(actual.current_predecessor, oracle.current_predecessor);
  failures += !equal(actual.current_successor, oracle.current_successor);
  failures += actual.receiver.program_identity != oracle.receiver.program_identity;
  failures += actual.receiver.obstruction != oracle.receiver.obstruction;
  failures += actual.receiver.all_deeds_returned != oracle.receiver.all_deeds_returned ||
      !actual.receiver.all_deeds_returned;
  failures += swing_failures(actual.receiver.swing, oracle.receiver.swing);
  failures += sameness_failures(actual.receiver.sameness, oracle.receiver.sameness);
  failures += projection_failures(actual.receiver.projection, oracle.receiver.projection);
  failures += connection_failures(actual.receiver.connection, oracle.receiver.connection);
  failures += hypergeometric_failures(actual.receiver.hypergeometric,
      oracle.receiver.hypergeometric);
  failures += carrier_failures(actual.receiver.carrier, oracle.receiver.carrier);
  failures += information_failures(actual.receiver.information, oracle.receiver.information);
  return failures;
}

}  // namespace holonics::tests
