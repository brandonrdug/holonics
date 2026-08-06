#include "r21_verify.hpp"

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

[[nodiscard]] std::uint16_t choose(std::uint8_t n, std::uint8_t k) noexcept {
  if (k > n) { return 0; }
  std::uint32_t value = 1;
  for (std::uint8_t step = 1; step <= k; ++step) {
    value = value * static_cast<std::uint32_t>(n + 1U - step) / step;
  }
  return static_cast<std::uint16_t>(value);
}

[[nodiscard]] std::size_t pair_failures(
    const organ::pair_incidence_receipt& pair, std::uint8_t distance) noexcept {
  std::size_t failures = !pair.exact || pair.distance != distance ||
      pair.left_size != distance + 1U || pair.right_size != 8U - distance ||
      pair.cell_count != pair.left_size * pair.right_size || !pair.equitable ||
      !pair.detailed_balance || !pair.directions_commute || !pair.characteristic_exact ||
      !pair.candidates[3].admitted;
  for (std::uint8_t source = 0; source < pair.cell_count; ++source) {
    const auto a = static_cast<std::uint8_t>(source / pair.right_size);
    const auto b = static_cast<std::uint8_t>(source % pair.right_size);
    failures += pair.population[source] !=
        choose(distance, a) * choose(static_cast<std::uint8_t>(7U - distance), b);
    for (std::uint8_t target = 0; target < pair.cell_count; ++target) {
      std::int16_t expected = 0;
      if (a > 0 && target == source - pair.right_size) { expected = a; }
      if (a + 1U < pair.left_size && target == source + pair.right_size) {
        expected = static_cast<std::int16_t>(distance - a);
      }
      if (b > 0 && target == source - 1U) { expected = b; }
      if (b + 1U < pair.right_size && target == source + 1U) {
        expected = static_cast<std::int16_t>(7U - distance - b);
      }
      failures += pair.quotient[source][target] != expected;
    }
  }
  std::uint8_t multiplicity = 0;
  for (std::uint8_t slot = 0; slot < 8; ++slot) {
    failures += pair.characteristic_roots[slot] != 7 - 2 * slot;
    multiplicity = static_cast<std::uint8_t>(multiplicity +
        pair.characteristic_multiplicity[slot]);
  }
  failures += multiplicity != pair.cell_count;
  return failures;
}

[[nodiscard]] std::size_t moment_failures(
    const organ::moment_root_receipt& value, const organ::moment_problem_case& source,
    const std::int64_t* roots, std::int64_t determinant) noexcept {
  std::size_t failures = !value.exact || !value.access_complete || !value.pencil_newton_agree ||
      !value.roots_remove_exactly || !value.vandermonde_square || !value.separable ||
      value.hankel_determinant != determinant || value.discriminant != determinant ||
      value.root_count != source.degree || !value.candidates[0].admitted;
  for (std::uint8_t row = 0; row < source.degree; ++row) {
    for (std::uint8_t column = 0; column < source.degree; ++column) {
      failures += value.hankel[row][column] != source.moments[row + column];
      failures += value.shifted[row][column] != source.moments[row + column + 1U];
    }
  }
  for (std::uint8_t slot = 0; slot < source.degree; ++slot) {
    failures += value.roots[slot] != roots[slot];
  }
  for (std::uint8_t slot = 1; slot < organ::blind_candidate_capacity; ++slot) {
    failures += value.candidates[slot].admitted;
  }
  return failures;
}

[[nodiscard]] std::size_t checker_failures(
    const event::blind_passage_return<codec::blind_code_face>& value) noexcept {
  return value.checker_stage != event::checker_stage_status::exact ||
      value.typed.state != event::checker_return_status::accepted ||
      value.typed.produced_declarations != 1 || value.typed.remaining_goal_count != 0 ||
      !value.typed.elaborator_boundary_crossed || !value.typed.kernel_boundary_crossed ||
      value.raw.exit_status != 0 || value.raw.stdout_bytes == 0 || value.raw.stderr_bytes != 0 ||
      value.raw.produced_artifact_bytes == 0 || !value.pending_before_process ||
      value.pending_after_return || !value.passage_preserved;
}

[[nodiscard]] std::size_t checker_failures(
    const event::blind_passage_return<codec::blind_moment_face>& value) noexcept {
  return value.checker_stage != event::checker_stage_status::exact ||
      value.typed.state != event::checker_return_status::accepted ||
      value.typed.produced_declarations != 1 || value.typed.remaining_goal_count != 0 ||
      !value.typed.elaborator_boundary_crossed || !value.typed.kernel_boundary_crossed ||
      value.raw.exit_status != 0 || value.raw.stdout_bytes == 0 || value.raw.stderr_bytes != 0 ||
      value.raw.produced_artifact_bytes == 0 || !value.pending_before_process ||
      value.pending_after_return || !value.passage_preserved;
}

}  // namespace

std::size_t r21_verification_failures(
    const apparatus::blind_store_receipt& code_load,
    const apparatus::blind_store_receipt& moment_load,
    const apparatus::blind_store_receipt& rest_load,
    const apparatus::blind_reconstruction_executor_receipt& execution,
    const apparatus::blind_probe_receipt& code_probe,
    const organ::blind_reconstruction_receipt& changed_code,
    const apparatus::blind_probe_receipt& moment_probe,
    const organ::blind_reconstruction_receipt& changed_moment,
    const event::blind_reconstruction_observation& actual,
    const event::blind_reconstruction_rest_record& handoff) noexcept {
  const auto& inquiry = actual.inquiry;
  std::size_t failures = !code_load.returned() || !moment_load.returned() ||
      !rest_load.returned() || !execution.returned() || !code_probe.returned() ||
      !moment_probe.returned() || execution.host_semantic_events != exact::word{0} ||
      execution.released_solution_reads != exact::word{0} ||
      execution.code_process.exterior_process_calls != exact::word{1} ||
      execution.moment_process.exterior_process_calls != exact::word{1};
  failures += !inquiry.theory_formed || !inquiry.all_exact ||
      inquiry.obstruction != organ::blind_obstruction::none || inquiry.returned_pairs != 3 ||
      inquiry.returned_moments != 5 || inquiry.separable_moments != 3 ||
      inquiry.obstructed_moments != 2 || !inquiry.no_released_solution_access ||
      !inquiry.no_expected_operator || !inquiry.no_expected_roots ||
      !inquiry.alternatives_retained;
  const std::uint16_t weights[8]{1, 0, 0, 7, 7, 0, 0, 1};
  const std::int64_t dual[8]{1, 0, 0, 0, 7, 0, 0, 0};
  failures += !inquiry.code.exact || inquiry.code.vertex_count != 128 ||
      inquiry.code.codeword_count != 16 || inquiry.code.minimum_distance != 3;
  for (std::uint8_t slot = 0; slot < 8; ++slot) {
    failures += inquiry.code.distance_distribution[slot] != weights[slot] ||
        inquiry.code.dual_distribution[slot] != dual[slot];
  }
  failures += pair_failures(inquiry.pairs[0], 3) + pair_failures(inquiry.pairs[1], 4) +
      pair_failures(inquiry.pairs[2], 7) || inquiry.pairs[0].lineage == inquiry.pairs[1].lineage ||
      inquiry.pairs[0].candidates[0].admitted || !inquiry.pairs[2].candidates[0].admitted;
  const std::int64_t roots0[3]{1, 2, 4};
  const std::int64_t roots1[3]{-2, 1, 3};
  const std::int64_t roots2[4]{0, 2, 5, 7};
  failures += moment_failures(inquiry.moments[0], inquiry.mounted_moments.cases[0], roots0, 36) +
      moment_failures(inquiry.moments[1], inquiry.mounted_moments.cases[1], roots1, 900) +
      moment_failures(inquiry.moments[2], inquiry.mounted_moments.cases[2], roots2, 4'410'000);
  failures += !inquiry.moments[3].exact || inquiry.moments[3].hankel_determinant != 0 ||
      inquiry.moments[3].discriminant != 0 ||
      inquiry.moments[3].obstruction != organ::blind_obstruction::singular_root_fiber ||
      !inquiry.moments[4].exact || inquiry.moments[4].access_complete ||
      inquiry.moments[4].obstruction != organ::blind_obstruction::moment_access_refused;
  bool code_changed = changed_code.code.codeword_count != inquiry.code.codeword_count;
  for (std::uint8_t slot = 0; slot < inquiry.code.codeword_count; ++slot) {
    code_changed = code_changed || changed_code.code.codewords[slot] != inquiry.code.codewords[slot];
  }
  const bool moment_changed = changed_moment.moments[0].hankel_determinant !=
      inquiry.moments[0].hankel_determinant ||
      changed_moment.moments[0].discriminant != inquiry.moments[0].discriminant;
  failures += !code_changed || !moment_changed;
  failures += checker_failures(actual.code) + checker_failures(actual.moment) ||
      !contains(actual.code.formal.bytes, actual.code.formal.byte_count,
          "theorem generated_tensor_jacobi_eigenvector") ||
      !contains(actual.moment.formal.bytes, actual.moment.formal.byte_count,
          "theorem generated_hankel_pencil") ||
      contains(actual.code.formal.bytes, actual.code.formal.byte_count, "sorry") ||
      contains(actual.moment.formal.bytes, actual.moment.formal.byte_count, "sorry");
  failures += actual.code.formation_commit.predecessor != exact::word{14'001'012} ||
      actual.code.formation_commit.successor != exact::word{14'001'013} ||
      actual.code.returned_morphology.commit.successor != exact::word{14'001'014} ||
      actual.moment.formation_commit.successor != exact::word{14'001'015} ||
      actual.moment.returned_morphology.commit.successor != exact::word{14'001'016} ||
      actual.code.returned_morphology.mathematical_after != 86 ||
      actual.moment.returned_morphology.mathematical_after != 94 ||
      actual.moment.returned_morphology.codec_after != 54;
  failures += !actual.rest.returned || !actual.rest.source_detached ||
      !actual.remount.same_body || !actual.remount.theories_preserved ||
      actual.remount.source_replayed || !actual.handoff.returned || !actual.final_can_continue ||
      actual.final_head != exact::word{14'001'016} ||
      actual.final_continuation != exact::word{15'001'016};
  failures += handoff.integrity != event::blind_reconstruction_rest_integrity(handoff) ||
      handoff.body.regions[0].morphology != 296 || handoff.mathematical_admitted_tally != 94 ||
      handoff.codec_admitted_tally != 54 || handoff.blind_reconstruction_admitted_tally != 24 ||
      handoff.code_reconstruction.identity != exact::word{188'300} ||
      !handoff.code_reconstruction.accepted ||
      handoff.moment_reconstruction.identity != exact::word{188'301} ||
      !handoff.moment_reconstruction.accepted || !handoff.regular_singular.accepted;
  return failures;
}

}  // namespace holonics::tests
