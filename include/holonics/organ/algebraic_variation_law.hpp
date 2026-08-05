#pragma once

#include <holonics/organ/variation_loop_law.hpp>

namespace holonics::organ::algebraic_variation_detail {

inline constexpr std::uint16_t family_dependency = 1U << 0U;
inline constexpr std::uint16_t reduction_dependency = 1U << 1U;
inline constexpr std::uint16_t connection_dependency = 1U << 2U;
inline constexpr std::uint16_t invariant_dependency = 1U << 3U;
inline constexpr std::uint16_t operator_dependency = 1U << 4U;
inline constexpr std::uint16_t loop_dependency = 1U << 5U;
inline constexpr std::uint16_t complete_dependencies = family_dependency |
    reduction_dependency | connection_dependency | invariant_dependency |
    operator_dependency | loop_dependency;

HOLONICS_CALLABLE constexpr void retain_section(theorem_selection_receipt& selection,
    std::uint16_t dependencies, std::uint16_t residuals,
    theorem_candidate_state state, std::uint64_t lineage) noexcept {
  auto& candidate = selection.candidates[selection.candidate_count];
  candidate.identity = exact::word{191'600U + selection.candidate_count};
  candidate.lineage = exact::word{lineage + selection.candidate_count};
  candidate.dependency_mask = dependencies; candidate.residual_mask = residuals;
  candidate.state = state; ++selection.candidate_count;
}

HOLONICS_CALLABLE constexpr void select_theorem(algebraic_variation_receipt& out) noexcept {
  if (!out.loops.exact) { out.obstruction = variation_obstruction::theorem_section_open; return; }
  const auto lineage = out.mounted.lineage.value() + 224U;
  retain_section(out.selection, family_dependency, reduction_dependency,
      theorem_candidate_state::incomplete_dependency, lineage);
  retain_section(out.selection, family_dependency | reduction_dependency |
      connection_dependency, invariant_dependency,
      theorem_candidate_state::holdout_refused, lineage);
  retain_section(out.selection, complete_dependencies & ~loop_dependency,
      loop_dependency, theorem_candidate_state::foil_refused, lineage);
  const bool foils = out.foils.squarefree_multiplicity_rejected &&
      out.foils.local_only_form_rejected && out.foils.euclidean_form_rejected &&
      out.foils.symmetric_form_rejected && out.foils.degenerate_form_rejected &&
      out.foils.operator_without_zeroth_rejected && out.foils.commuting_loops_rejected &&
      out.foils.equal_spectrum_not_equal_collision;
  const bool holdouts = out.connection.holdouts_exact && out.scalar.holdouts_exact;
  retain_section(out.selection, complete_dependencies, foils && holdouts ? 0 : 1,
      foils && holdouts ? theorem_candidate_state::selected :
      theorem_candidate_state::holdout_refused, lineage);
  auto& selected = out.selection.candidates[3];
  out.selection.selected = selected.state == theorem_candidate_state::selected ?
      selected.identity : exact::word{};
  out.selection.lineage = exact::word{lineage}; out.selection.no_score = true;
  out.selection.no_expected_statement = true; out.selection.holdout_closed = holdouts;
  out.selection.foils_closed = foils;
  out.selection.exact = out.selection.selected.value() != 0 &&
      selected.dependency_mask == complete_dependencies && selected.residual_mask == 0;
  if (!out.selection.exact) { out.obstruction = variation_obstruction::theorem_section_open; }
}

HOLONICS_CALLABLE constexpr void close(algebraic_variation_receipt& out) noexcept {
  out.no_expected_names = true; out.alternatives_retained = out.selection.candidate_count == 4 &&
      out.invariant.retained_count >= 5;
  out.theory = algebraic_variation_plan{exact::word{191'620}, out.selection.selected,
      exact::word{out.selection.lineage.value() + 1U}, out.discriminant_exact,
      out.connection.exact, out.invariant.exact, out.scalar.exact, out.loops.exact,
      out.selection.exact};
  out.theory_formed = out.selection.exact;
  out.all_exact = out.obstruction == variation_obstruction::none && out.roots_exact &&
      out.discriminant_exact && out.connection.exact && out.invariant.exact &&
      out.scalar.exact && out.loops.exact && out.selection.exact &&
      out.alternatives_retained && out.no_expected_names;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr algebraic_variation_receipt derive(
    const algebraic_variation_foundation& foundation,
    algebraic_variation_question question) noexcept {
  algebraic_variation_receipt out{}; out.question = question;
  variation_polynomial_detail::derive_family(foundation, out);
  variation_connection_detail::derive_connection(out);
  variation_invariant_detail::derive_invariant(out);
  variation_operator_detail::derive_scalar(out);
  variation_loop_detail::derive_loops(out);
  select_theorem(out); close(out); return out;
}

}  // namespace holonics::organ::algebraic_variation_detail
