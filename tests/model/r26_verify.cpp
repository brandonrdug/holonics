#include "r26_verify.hpp"

namespace holonics::tests {
namespace {

template<std::size_t Capacity, class Count, std::size_t Pattern>
[[nodiscard]] bool contains(const char (&bytes)[Capacity], Count used,
    const char (&pattern)[Pattern]) noexcept {
  constexpr std::size_t width = Pattern - 1U;
  for (std::size_t start = 0; width != 0 && start + width <= used; ++start) {
    bool same = true;
    for (std::size_t slot = 0; slot < width; ++slot) {
      same = same && bytes[start + slot] == pattern[slot];
    }
    if (same) { return true; }
  }
  return false;
}

[[nodiscard]] std::uint16_t host_gcd(std::uint16_t left, std::uint16_t right) noexcept {
  while (right != 0) {
    const auto held = static_cast<std::uint16_t>(left % right); left = right; right = held;
  }
  return left;
}

[[nodiscard]] std::uint8_t host_seam(std::uint16_t first, std::uint16_t second,
    std::uint16_t m, std::uint16_t n) noexcept {
  const bool first_wrap = first + 1U == m; const bool second_wrap = second + 1U == n;
  return static_cast<std::uint8_t>((first_wrap ? 1U : 0U) | (second_wrap ? 2U : 0U));
}

[[nodiscard]] std::size_t case_failures(
    const organ::intrinsic_phase_case_receipt& value) noexcept {
  const auto m = value.presentation.first; const auto n = value.presentation.second;
  const auto vertices = static_cast<std::uint16_t>(m * n); const auto divisor = host_gcd(m, n);
  const auto lcm = static_cast<std::uint16_t>((m / divisor) * n);
  std::size_t failures = !value.exact || value.vertex_count != vertices ||
      value.edge_count != 2U * vertices || value.face_count != vertices ||
      value.flag_count != 8U * vertices || value.gcd != divisor || value.lcm != lcm ||
      value.tour_count != divisor || value.recurrence_depth !=
          static_cast<std::uint16_t>((m > n ? m : n) + 1U) ||
      !value.coordinates_exact || !value.incidence_exact || !value.stars_links_exact ||
      !value.boundaries_exact || !value.seams_shared_exact || !value.chronology_exact ||
      !value.projection_fibers_complete || !value.distributions_exact || !value.sections_exact;
  std::uint32_t expected[4][4]{}; std::uint16_t seam_population[4]{};
  for (std::uint16_t first = 0; first < m; ++first) {
    for (std::uint16_t second = 0; second < n; ++second) {
      const auto seam = host_seam(first, second, m, n);
      const auto next_first = static_cast<std::uint16_t>(first + 1U == m ? 0U : first + 1U);
      const auto next_second = static_cast<std::uint16_t>(second + 1U == n ? 0U : second + 1U);
      const auto next = host_seam(next_first, next_second, m, n);
      ++seam_population[seam]; ++expected[seam][next];
    }
  }
  std::uint16_t projection_population = 0;
  for (std::uint16_t fiber = 0; fiber < value.projection_fiber_count; ++fiber) {
    projection_population = static_cast<std::uint16_t>(
        projection_population + value.projection_fiber_sizes[fiber]);
  }
  failures += projection_population != vertices;
  for (std::uint8_t row = 0; row < 4; ++row) {
    failures += seam_population[row] != value.seam_receiver_fibers[row];
    for (std::uint8_t column = 0; column < 4; ++column) {
      failures += expected[row][column] != value.transition_population[row][column];
    }
  }
  for (std::uint16_t edge = 0; edge < value.edge_count; ++edge) {
    failures += value.edges[edge].source >= vertices || value.edges[edge].target >= vertices ||
        value.edges[edge].incident_faces[0] >= vertices ||
        value.edges[edge].incident_faces[1] >= vertices ||
        value.edges[edge].incident_orientation[0] +
            value.edges[edge].incident_orientation[1] != 0;
  }
  for (std::uint16_t face = 0; face < value.face_count; ++face) {
    failures += !value.faces[face].boundary_closes || !value.faces[face].filled;
  }
  for (std::uint8_t tour = 0; tour < value.tour_count; ++tour) {
    failures += value.tours[tour].length != lcm || !value.tours[tour].determinant_one;
  }
  return failures;
}

[[nodiscard]] std::size_t mathematical_failures(
    const event::intrinsic_hypergeometry_observation& actual) noexcept {
  const auto& value = actual.inquiry;
  std::size_t failures = !value.all_exact || !value.theory_formed ||
      value.source_mask != 0x0fffU || !value.source_currents_independent ||
      !value.no_expected_invariants || !value.alternatives_retained ||
      value.obstruction != organ::intrinsic_hypergeometry_obstruction::none;
  for (std::uint8_t slot = 0; slot < organ::intrinsic_case_capacity; ++slot) {
    failures += case_failures(value.cases[slot]);
  }
  failures += !value.series.recurrence_exact || value.series.count != 20 ||
      !value.local_system.exact || !value.local_system.form_preserved ||
      !value.local_system.alternatives_unequal || !value.local_system.commutator_nontrivial ||
      value.local_system.commutator[0][0] != 13 ||
      value.local_system.commutator[0][1] != 8 ||
      value.local_system.commutator[1][0] != 8 ||
      value.local_system.commutator[1][1] != 5;
  failures += !value.supported.exact || value.supported.square_count != 40 ||
      !value.supported.common_cycle_characteristic ||
      !value.supported.phase_cycle_is_boundary || !value.supported.cm_cycle_has_no_two_cell ||
      !value.supported.filled_extension_obstructed || !value.supported.supported_loop_admitted;
  const std::int64_t characteristic[5]{1,0,0,0,-1};
  for (std::uint8_t slot = 0; slot < 5; ++slot) {
    failures += value.supported.phase_characteristic.coefficients[slot] != characteristic[slot] ||
        value.supported.cm_characteristic.coefficients[slot] != characteristic[slot];
  }
  for (const auto population : value.supported.cm_edge_square_population) {
    failures += population != 4;
  }
  failures += !value.controls.exact || !value.controls.equal_hull_unequal_transport ||
      !value.controls.equal_local_population_unequal_order ||
      !value.controls.equal_spectrum_unequal_support || !value.controls.conjugate_rechart ||
      !value.controls.changed_source_sensitive || !actual.changed_sensitive ||
      case_failures(actual.changed_case) != 0 || actual.changed_case.vertex_count != 40 ||
      actual.changed_case.edge_count != 80 || actual.changed_case.face_count != 40 ||
      actual.changed_case.flag_count != 320 || actual.changed_case.lcm != 40 ||
      actual.changed_case.tour_count != 1;
  return failures;
}

}  // namespace

std::size_t r26_verification_failures(bool sources_loaded,
    const apparatus::intrinsic_hypergeometry_store_receipt& rest_load,
    const apparatus::intrinsic_hypergeometry_executor_receipt& execution,
    const event::intrinsic_hypergeometry_observation& actual,
    const event::intrinsic_hypergeometry_rest_record& handoff) noexcept {
  std::size_t failures = !sources_loaded || !rest_load.returned() || !execution.returned() ||
      execution.host_semantic_events != exact::word{0} ||
      execution.semantic_threads != exact::word{23} ||
      execution.process.exterior_process_calls != exact::word{1};
  failures += mathematical_failures(actual); const auto& passage = actual.passage;
  failures += passage.checker_stage != event::checker_stage_status::exact ||
      passage.typed.state != event::checker_return_status::accepted ||
      passage.typed.produced_declarations != 1 || passage.typed.remaining_goal_count != 0 ||
      !passage.typed.elaborator_boundary_crossed || !passage.typed.kernel_boundary_crossed ||
      passage.raw.exit_status != 0 || passage.raw.stdout_bytes == 0 ||
      passage.raw.stderr_bytes != 0 || passage.raw.produced_artifact_bytes == 0 ||
      !passage.pending_before_process || passage.pending_after_return ||
      !passage.passage_preserved || !contains(passage.formal.bytes,
          passage.formal.byte_count, "theorem generated_intrinsic_archetype_calculus") ||
      contains(passage.formal.bytes, passage.formal.byte_count, "sorry");
  failures += passage.formation_commit.predecessor != exact::word{14'001'024} ||
      passage.formation_commit.successor != exact::word{14'001'025} ||
      passage.returned_morphology.commit.successor != exact::word{14'001'026} ||
      passage.returned_morphology.mathematical_after != 164 ||
      passage.returned_morphology.codec_after != 84;
  failures += !actual.rest.returned || !actual.rest.source_detached ||
      !actual.remount.same_body || !actual.remount.theory_preserved ||
      actual.remount.source_replayed || !actual.handoff.returned ||
      !actual.final_can_continue || actual.final_head != exact::word{14'001'026} ||
      actual.final_continuation != exact::word{15'001'026};
  failures += handoff.integrity != event::intrinsic_hypergeometry_rest_integrity(handoff) ||
      handoff.body.regions[0].admitted_tally != 535 || handoff.mathematical_admitted_tally != 164 ||
      handoff.codec_admitted_tally != 84 || handoff.causal_linear_admitted_tally != 29 ||
      handoff.intrinsic_hypergeometry_admitted_tally != 31 ||
      handoff.intrinsic_hypergeometry.identity != exact::word{193'300} ||
      !handoff.intrinsic_hypergeometry.accepted || !handoff.causal_linear.accepted;
  return failures;
}

}  // namespace holonics::tests
