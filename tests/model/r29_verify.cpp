#include "r29_verify.hpp"

#include "r29_reference.hpp"

namespace holonics::tests {
namespace {
template<std::size_t Capacity, class Count, std::size_t Pattern>
[[nodiscard]] bool contains(const char (&bytes)[Capacity], Count used,
    const char (&pattern)[Pattern]) noexcept {
  constexpr std::size_t width = Pattern - 1U;
  for (std::size_t start = 0; width != 0 && start + width <= used; ++start) {
    bool same = true;
    for (std::size_t slot = 0; slot < width; ++slot) { same = same && bytes[start + slot] == pattern[slot]; }
    if (same) { return true; }
  }
  return false;
}

[[nodiscard]] std::size_t field_failures(const organ::arithmetic_spectral_receipt& actual,
    const r29_reference_result& reference) noexcept {
  std::size_t failures = 0;
  for (std::uint8_t tower = 0; tower < organ::arithmetic_base_count; ++tower) {
    failures += !actual.towers[tower].exact;
    for (std::uint8_t degree = 0; degree < organ::arithmetic_degree_count; ++degree) {
      const auto& left = actual.towers[tower].fields[degree];
      const auto& right = reference.fields[tower][degree];
      failures += !left.irreducible || left.prime != right.p || left.degree != right.degree ||
          left.order != right.q;
      for (std::uint8_t slot = 0; slot <= degree + 1U; ++slot) {
        failures += left.modulus[slot] != right.modulus[slot];
      }
    }
  }
  return failures;
}

[[nodiscard]] std::size_t curve_failures(const organ::arithmetic_spectral_receipt& actual,
    const r29_reference_result& reference) noexcept {
  std::size_t failures = 0;
  for (std::uint8_t curve = 0; curve < organ::arithmetic_curve_count; ++curve) {
    const auto& left = actual.curves[curve]; const auto& right = reference.curves[curve];
    failures += !left.exact || left.source.prime != right.prime ||
        left.source.coefficient != right.coefficient || left.frobenius.real != right.real ||
        left.frobenius.imaginary != right.imaginary || left.pointwise_points != right.quadratic_points ||
        !left.correspondence_precedes_matrix || !left.degree_bound_closes || !left.forms_exact ||
        !left.weight_exact || !left.fixed_trace_agrees || !left.functional_relation ||
        !left.primary_exact || !left.euler_prefix_exact;
    for (std::uint8_t degree = 0; degree < organ::arithmetic_degree_count; ++degree) {
      failures += left.fixed_counts[degree] != right.counts[degree];
    }
  }
  return failures;
}

[[nodiscard]] std::size_t workspace_failures(const organ::arithmetic_spectral_receipt& actual,
    const organ::arithmetic_spectral_workspace& workspace) noexcept {
  std::size_t failures = 0; std::uint32_t fixed_sums[organ::arithmetic_curve_count][4]{};
  for (const auto& receipt : workspace.fixed) {
    failures += receipt.curve >= organ::arithmetic_curve_count || receipt.degree < 1 ||
        receipt.degree > 4 || receipt.character < -1 || receipt.character > 1 ||
        receipt.point_count != static_cast<std::uint8_t>(receipt.character + 1) ||
        receipt.lineage.value() == 0;
    if (receipt.curve < organ::arithmetic_curve_count && receipt.degree >= 1 && receipt.degree <= 4) {
      fixed_sums[receipt.curve][receipt.degree - 1U] += receipt.point_count;
    }
  }
  for (std::uint8_t curve = 0; curve < organ::arithmetic_curve_count; ++curve) {
    std::uint8_t selected = 0;
    for (const auto& candidate : workspace.candidates[curve]) {
      failures += candidate.curve != curve || candidate.lineage.value() == 0;
      if (candidate.selected) {
        ++selected; failures += !candidate.norm_matches || candidate.mismatches != 0;
      }
    }
    failures += selected != 1; std::uint32_t points = 0;
    for (const auto& point : workspace.points) {
      if (point.curve == curve && point.on_curve) { ++points; failures += !point.equal; }
    }
    failures += points != actual.curves[curve].fixed_counts[1];
    for (std::uint8_t degree = 0; degree < 4; ++degree) {
      failures += 1U + fixed_sums[curve][degree] != actual.curves[curve].fixed_counts[degree];
    }
    for (const auto& current : workspace.trace_currents[curve]) {
      failures += current.curve != curve || current.residual != 0 || current.lineage.value() == 0;
    }
    for (const auto& current : workspace.norm_currents[curve]) {
      failures += current.curve != curve || !current.nonnegative || current.norm < 0 ||
          current.lineage.value() == 0;
    }
  }
  return failures;
}

}  // namespace

std::size_t r29_verification_failures(bool source_loaded,
    const apparatus::arithmetic_store_receipt& rest_load,
    const apparatus::arithmetic_executor_receipt& execution,
    const event::arithmetic_spectral_observation& observation,
    const organ::arithmetic_spectral_workspace& workspace,
    const event::arithmetic_spectral_rest_record& handoff) noexcept {
  const auto reference = r29_reference(); std::size_t failures = !source_loaded ||
      !rest_load.returned() || !execution.returned() || !reference.exact ||
      execution.host_semantic_events != exact::word{0} ||
      execution.semantic_threads != exact::word{302'612} || execution.kernel_launches != exact::word{13} ||
      execution.process.exterior_process_calls != exact::word{1};
  failures += field_failures(observation.inquiry, reference);
  failures += curve_failures(observation.inquiry, reference);
  failures += workspace_failures(observation.inquiry, workspace);
  failures += !observation.inquiry.all_exact || !observation.inquiry.theory_formed ||
      observation.inquiry.obstruction != organ::arithmetic_spectral_obstruction::none ||
      !observation.inquiry.no_expected_invariants || !observation.inquiry.alternatives_retained;
  const auto& passage = observation.passage;
  failures += passage.typed.state != event::checker_return_status::accepted ||
      passage.raw.exit_status != 0 || passage.raw.stdout_bytes == 0 || passage.raw.stderr_bytes != 0 ||
      !passage.pending_before_process || passage.pending_after_return || !passage.passage_preserved ||
      !contains(passage.formal.bytes, passage.formal.byte_count,
          "theorem generated_arithmetic_spectral_placement") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "smoothnessStatement") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "recurrenceCountStatement") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "zetaDualityStatement") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "eulerCoefficientStatement") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "primaryEigenvectorStatement") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "explicitFormulaStatement") ||
      !contains(passage.formal.bytes, passage.formal.byte_count, "positiveCurrentStatement") ||
      contains(passage.formal.bytes, passage.formal.byte_count, "sorry");
  failures += passage.formation_commit.predecessor != exact::word{14'001'030} ||
      passage.formation_commit.successor != exact::word{14'001'031} ||
      passage.returned_morphology.commit.successor != exact::word{14'001'032} ;
  failures += !observation.rest.returned || !observation.rest.source_detached ||
      !observation.remount.same_body || !observation.remount.theory_preserved ||
      observation.remount.source_replayed || !observation.handoff.returned ||
      !observation.final_can_continue || observation.final_head != exact::word{14'001'032} ||
      observation.final_continuation != exact::word{15'001'032};
  failures += handoff.integrity != event::arithmetic_spectral_rest_integrity(handoff) ||
      handoff.arithmetic_spectral.identity != exact::word{196'300} ||
      !handoff.arithmetic_spectral.accepted || !handoff.hodge_realization.accepted;
  return failures;
}

}  // namespace holonics::tests
