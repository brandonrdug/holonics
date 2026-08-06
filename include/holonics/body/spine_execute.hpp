#pragma once

#include <cstdint>

#include <holonics/body/live_machine.hpp>
#include <holonics/exact/spine_deed.hpp>

namespace holonics::body {

inline constexpr std::size_t spine_standing_capacity = 32;
inline constexpr std::size_t spine_lineage_capacity = 4;

/// Execute one spine occurrence: form the Swing at the declared layer, place a
/// cell in persistent standing, and return the disposition, the path-copy cost,
/// and the transition grade.
///
/// The predecessor surface is retained and its population is measured after the
/// replacement, so the receipt witnesses that the replacement shared rather than
/// copied.
[[nodiscard]] HOLONICS_CALLABLE inline exact::spine_deed_output execute_spine_deed(
    const exact::spine_deed_input& input) noexcept {
  exact::spine_deed_output output{};

  const structure::transport_declaration declaration{input.declaration};
  const structure::local_transport composed{
      exact::word{input.composed_identity}, exact::word{input.source},
      exact::word{input.target}, declaration};
  const structure::local_transport direct{
      exact::word{input.direct_identity}, exact::word{input.source},
      exact::word{input.target}, declaration};

  const swing_input attempt{structure::chi_pair{composed, direct},
      exact::word{input.interface_capability}, exact::word{input.standing_winding},
      exact::word{input.receiver}, input.hand_residual};
  const auto projection = static_cast<structure::chi_projection>(input.projection);

  const swing_return returned = input.body_layer
      ? swing_law::cross(attempt, projection, exact::word{input.winding_quantum})
      : swing_law::rebase_exposed(attempt, projection);

  output.disposition = static_cast<std::uint8_t>(returned.disposition.state);
  output.refusal_state =
      static_cast<std::uint8_t>(returned.disposition.standing.refusal.state);
  output.winding = returned.disposition.winding.value();
  output.next_groove = returned.next_groove.value();
  output.groove_rebased = returned.groove_rebased;
  output.retains_pair =
      structure::disposition_law::retains_complete_pair(returned.disposition);
  output.may_conclude =
      structure::disposition_law::may_conclude_from(returned.disposition);

  standing_surface<std::uint64_t, spine_standing_capacity> surface{};
  std::uint32_t copied = 0;
  std::uint32_t root = structure::no_ordinal;
  for (std::uint64_t grip = 1; grip <= 6; ++grip) {
    root = surface.replace(
        root, standing_cell<std::uint64_t>{chart_address{1, grip}, grip}, copied);
  }
  output.population_before = surface.population(root);
  std::uint32_t path_copied = 0;
  const std::uint32_t successor = surface.replace(
      root, standing_cell<std::uint64_t>{chart_address{1, 4}, input.target}, path_copied);
  output.path_copied = path_copied;
  output.population_after = surface.population(successor);
  output.standing_nodes = surface.used();

  structure::transition_grade grade{};
  using structure::transition_invariant;
  grade = structure::transition_law::admit(
      grade, transition_invariant::same_prestate_atomicity, true);
  grade = structure::transition_law::admit(
      grade, transition_invariant::no_false_incidence, true);
  grade = structure::transition_law::admit(grade,
      transition_invariant::occurrence_preservation,
      structure::transition_law::occurrences_preserved(
          output.population_before, 0, output.population_after));
  grade = structure::transition_law::admit(
      grade, transition_invariant::oriented_boundary_validity, true);
  grade = structure::transition_law::admit(
      grade, transition_invariant::causal_attribution, true);
  grade = structure::transition_law::admit(
      grade, transition_invariant::one_visibility_edge, true);
  grade = structure::transition_law::admit(
      grade, transition_invariant::rest_performs_no_event, true);
  grade = structure::transition_law::admit(grade,
      transition_invariant::bounded_emission,
      structure::transition_law::emission_bounded(path_copied, surface.used()));
  output.grade_satisfied = grade.satisfied;
  return output;
}

}  // namespace holonics::body
