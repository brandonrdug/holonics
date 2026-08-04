#include "r22_verify.hpp"

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

[[nodiscard]] std::size_t arithmetic_failures(
    const organ::cm_incidence_receipt& value) noexcept {
  const std::int64_t roots[5][4]{{1,0,0,0}, {0,1,0,0}, {0,0,1,0},
      {0,0,0,1}, {-1,-1,-1,-1}};
  const std::uint8_t masks[5]{1,2,4,8,15};
  std::size_t failures = value.returned_translations != 5;
  for (std::uint8_t direction = 0; direction < 5; ++direction) {
    failures += !value.translations[direction].exact ||
        !value.translations[direction].norm_one ||
        value.translations[direction].residue_mask != masks[direction];
    for (std::uint8_t slot = 0; slot < 4; ++slot) {
      failures += value.translations[direction].value.coefficients[slot] !=
          roots[direction][slot];
      failures += value.translations[direction].norm.coefficients[slot] !=
          (slot == 0 ? 1 : 0);
    }
  }
  return failures;
}

[[nodiscard]] std::size_t graph_failures(
    const organ::cm_incidence_receipt& value) noexcept {
  const std::int64_t periodic[17]{1,0,-40,0,540,-384,-3480,5760,8070,-29440,
      17640,37120,-82020,74880,-37800,10368,-1215};
  const std::int64_t window[17]{1,0,-33,0,376,-48,-1984,576,4992,-2304,-4864,
      3072,0,0,0,0,0};
  std::size_t failures = !value.periodic.exact || !value.window.exact ||
      !value.periodic.characteristic_exact || !value.window.characteristic_exact ||
      value.periodic.edge_count != 40 || value.window.edge_count != 33 ||
      value.periodic.factor_count != 3 || value.window.factor_count != 5;
  const std::uint8_t directions[5]{8,8,8,8,1};
  for (std::uint8_t slot = 0; slot < 17; ++slot) {
    failures += value.periodic.characteristic[slot] != periodic[slot] ||
        value.window.characteristic[slot] != window[slot];
  }
  for (std::uint8_t direction = 0; direction < 5; ++direction) {
    failures += value.projection.direction_population[direction] != directions[direction];
  }
  const std::int16_t eigenvalues[16]{5,1,1,1,1,1,1,-3,1,1,1,-3,1,-3,-3,-3};
  for (std::uint8_t frequency = 0; frequency < 16; ++frequency) {
    failures += value.periodic.character_eigenvalue[frequency] != eigenvalues[frequency];
  }
  for (std::uint8_t source = 0; source < 16; ++source) {
    failures += value.periodic.degree[source] != 5;
    for (std::uint8_t target = static_cast<std::uint8_t>(source + 1); target < 16;
        ++target) {
      std::size_t common = 0;
      for (std::uint8_t middle = 0; middle < 16; ++middle) {
        common += value.periodic.adjacency[source][middle] != 0 &&
            value.periodic.adjacency[target][middle] != 0;
      }
      failures += common != (value.periodic.adjacency[source][target] != 0 ? 0U : 2U);
      const auto difference = static_cast<std::uint8_t>(source ^ target);
      const bool periodic_contact = difference == 1 || difference == 2 ||
          difference == 4 || difference == 8 || difference == 15;
      const bool window_contact = difference == 1 || difference == 2 ||
          difference == 4 || difference == 8 || (source == 0 && target == 15);
      failures += (value.periodic.adjacency[source][target] != 0) != periodic_contact ||
          (value.window.adjacency[source][target] != 0) != window_contact;
    }
  }
  failures += value.periodic.factors[0].coefficients[1] != 3 ||
      value.periodic.factors[0].multiplicity != 5 ||
      value.periodic.factors[1].coefficients[1] != -1 ||
      value.periodic.factors[1].multiplicity != 10 ||
      value.periodic.factors[2].coefficients[1] != -5 ||
      value.window.factors[0].coefficients[1] != 2 ||
      value.window.factors[0].multiplicity != 3 ||
      value.window.factors[1].coefficients[1] != 0 ||
      value.window.factors[1].multiplicity != 5 ||
      value.window.factors[2].coefficients[1] != -2 ||
      value.window.factors[2].multiplicity != 3 ||
      value.window.factors[3].coefficients[1] != 1 ||
      value.window.factors[3].coefficients[2] != -4 ||
      value.window.factors[4].coefficients[1] != -1 ||
      value.window.factors[4].coefficients[2] != -16 ||
      value.window.factors[4].coefficients[3] != 12;
  return failures;
}

[[nodiscard]] std::size_t receiver_failures(
    const organ::cm_incidence_receipt& value) noexcept {
  std::size_t failures = !value.projection.exact || !value.projection.basis_injective ||
      !value.projection.factor_expansion_agree || value.projection.unit_pair_count != 33 ||
      value.projection.lost_count != 7 || value.projection.projection_loss != 0 ||
      value.projection.distinct_scalar_sums != 5 || !value.scattering.exact ||
      !value.scattering.interchange_broken;
  for (std::uint8_t axis = 0; axis < 4; ++axis) {
    failures += value.scattering.commutator_nonzero[axis] != 4 ||
        value.scattering.commutator_square[axis] != 4;
  }
  for (const auto& candidate : value.candidates) { failures += candidate.admitted; }
  return failures;
}

}  // namespace

std::size_t r22_verification_failures(const apparatus::cm_store_receipt& card_load,
    const apparatus::cm_store_receipt& rest_load,
    const apparatus::cm_executor_receipt& execution,
    const apparatus::cm_probe_receipt& probe,
    const organ::cm_incidence_receipt& changed,
    const event::cm_incidence_observation& actual,
    const event::cm_incidence_rest_record& handoff) noexcept {
  const auto& inquiry = actual.inquiry;
  std::size_t failures = !card_load.returned() || !rest_load.returned() ||
      !execution.returned() || !probe.returned() ||
      execution.host_semantic_events != exact::word{0} ||
      execution.process.exterior_process_calls != exact::word{1};
  failures += !inquiry.theory_formed || !inquiry.all_exact ||
      inquiry.obstruction != organ::cm_obstruction::none ||
      !inquiry.no_expected_incidence || !inquiry.no_expected_spectrum ||
      !inquiry.alternatives_retained;
  failures += arithmetic_failures(inquiry) + graph_failures(inquiry) +
      receiver_failures(inquiry);
  failures += changed.returned_translations != 4 || changed.periodic.edge_count != 32 ||
      changed.window.edge_count != 32 || changed.projection.lost_count != 0 ||
      !changed.periodic.exact || !changed.window.exact ||
      !changed.periodic.characteristic_exact || !changed.window.characteristic_exact ||
      !changed.projection.factor_expansion_agree ||
      changed.periodic.factor_count != 5 || changed.window.factor_count != 5 ||
      changed.periodic.characteristic[2] == inquiry.periodic.characteristic[2];
  const std::int64_t probe_characteristic[17]{1,0,-32,0,352,0,-1792,0,4352,0,
      -4096,0,0,0,0,0,0};
  for (std::uint8_t slot = 0; slot < 17; ++slot) {
    failures += changed.periodic.characteristic[slot] !=
        changed.window.characteristic[slot] ||
        changed.periodic.characteristic[slot] != probe_characteristic[slot];
  }
  const auto& passage = actual.passage;
  failures += passage.checker_stage != event::checker_stage_status::exact ||
      passage.typed.state != event::checker_return_status::accepted ||
      passage.typed.produced_declarations != 1 || passage.typed.remaining_goal_count != 0 ||
      !passage.typed.elaborator_boundary_crossed || !passage.typed.kernel_boundary_crossed ||
      passage.raw.exit_status != 0 || passage.raw.stdout_bytes == 0 ||
      passage.raw.stderr_bytes != 0 || passage.raw.produced_artifact_bytes == 0 ||
      !passage.pending_before_process || passage.pending_after_return ||
      !passage.passage_preserved ||
      !contains(passage.formal.bytes, passage.formal.byte_count,
          "theorem generated_cm_characteristic_transport") ||
      contains(passage.formal.bytes, passage.formal.byte_count, "sorry");
  failures += passage.formation_commit.predecessor != exact::word{14'001'016} ||
      passage.formation_commit.successor != exact::word{14'001'017} ||
      passage.returned_morphology.commit.successor != exact::word{14'001'018} ||
      passage.returned_morphology.mathematical_after != 104 ||
      passage.returned_morphology.codec_after != 58;
  failures += !actual.rest.returned || !actual.rest.source_detached ||
      !actual.remount.same_body || !actual.remount.theory_preserved ||
      actual.remount.source_replayed || !actual.handoff.returned ||
      !actual.final_can_continue || actual.final_head != exact::word{14'001'018} ||
      actual.final_continuation != exact::word{15'001'018};
  failures += handoff.integrity != event::cm_incidence_rest_integrity(handoff) ||
      handoff.body.regions[0].morphology != 327 ||
      handoff.mathematical_morphology != 104 || handoff.codec_morphology != 58 ||
      handoff.cm_incidence_morphology != 17 ||
      handoff.cm_incidence.identity != exact::word{189'300} ||
      !handoff.cm_incidence.accepted || !handoff.moment_reconstruction.accepted;
  return failures;
}

}  // namespace holonics::tests
