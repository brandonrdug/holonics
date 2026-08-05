#pragma once

#include <holonics/organ/trace_rebase_close_law.hpp>

namespace holonics::organ::heldout_trace_rebase_detail {

HOLONICS_CALLABLE inline void form_source(
    const heldout_trace_rebase_card &card,
    heldout_trace_rebase_source &out) noexcept {
  out = {};
  out.lineage = card.metadata.lineage;
  out.path_length = card.path_length;
  for (std::uint8_t i = 0; i < 3; ++i)
    out.matrices[0][i] = card.seed[i];
  trace_rebase_matrix_detail::coordinates(out.matrices[0], out.coordinates[0]);
  bool exact = card.metadata.parsed && card.path_length >= 8 &&
               card.path_length <= trace_rebase_heldout_path_capacity &&
               trace_rebase_matrix_detail::valid(out.matrices[0]);
  for (std::uint8_t step = 0; step < card.path_length; ++step) {
    trace_rebase_matrix_detail::apply(card.moves[step], out.matrices[step],
                                      out.matrices[step + 1U]);
    trace_rebase_matrix_detail::coordinates(out.matrices[step + 1U],
                                            out.coordinates[step + 1U]);
    exact = exact && trace_rebase_matrix_detail::valid(out.matrices[step + 1U]);
  }
  out.valid = exact;
}
HOLONICS_CALLABLE inline void expose(
    const heldout_trace_rebase_source &source,
    heldout_trace_rebase_receipt &out) noexcept {
  out = {};
  out.path_length = source.path_length;
  out.lineage = source.lineage;
  for (std::uint8_t i = 0; i < trace_rebase_coordinate_count; ++i)
    out.predicted[0][i] = source.coordinates[0][i];
  out.source_detached = true;
}
[[nodiscard]] HOLONICS_CALLABLE inline bool founded(
    const trace_rebase_map_organ (&maps)[trace_rebase_move_count]) noexcept {
  bool exact = true;
  for (const auto &map : maps)
    exact = exact && map.primitive && map.checker_founded &&
            map.identity.value() != 0;
  return exact;
}
[[nodiscard]] HOLONICS_CALLABLE inline bool founded_predict(
    const trace_rebase_map_organ &map, const std::int64_t *source,
    std::int64_t (&target)[trace_rebase_coordinate_count]) noexcept {
  return map.identity.value() != 0 && map.checker_founded && map.primitive &&
         trace_rebase_close_detail::map_predict(map, source, target);
}
HOLONICS_CALLABLE inline void predict(
    const heldout_trace_rebase_card &card,
    const trace_fiber_organ (&fiber)[2],
    const trace_rebase_map_organ (&maps)[trace_rebase_move_count],
    heldout_trace_rebase_receipt &out) noexcept {
  out.passage = exact::word{202'420};
  if (!fiber[0].checker_founded || !fiber[1].checker_founded) {
    out.lift_exclusion = trace_rebase_obstruction::lift_organ_absent;
    return;
  }
  if (!founded(maps)) {
    out.map_exclusion = trace_rebase_obstruction::map_organ_absent;
    return;
  }
  bool exact = out.path_length >= 8 &&
               out.path_length <= trace_rebase_heldout_path_capacity;
  for (std::uint8_t step = 0; step < out.path_length; ++step)
    out.moves[step] = card.moves[step];
  for (std::uint8_t step = 0; step <= out.path_length; ++step) {
    std::int64_t gradient[trace_rebase_coordinate_count]{};
    std::int64_t basis[trace_rebase_tangent_rank]
                      [trace_rebase_coordinate_count]{};
    exact = exact && trace_rebase_differential_detail::gradient(
                         fiber[0], fiber[1],
                         out.predicted[step], gradient);
    out.tangent_rank[step] =
        trace_rebase_differential_detail::tangent(gradient, basis);
    out.vertical_rank[step] = gradient[6] == 0 ? 1U : 0U;
    out.branch[step] = out.vertical_rank[step] == 1;
    if (step == out.path_length)
      continue;
    const auto move = static_cast<std::uint8_t>(card.moves[step]);
    const bool formed = founded_predict(
        maps[move], out.predicted[step], out.predicted[step + 1U]);
    out.step_obstruction[step] =
        formed ? trace_rebase_obstruction::none
               : trace_rebase_obstruction::map_organ_absent;
    std::int64_t target_gradient[trace_rebase_coordinate_count]{},
        jacobian[trace_rebase_coordinate_count][trace_rebase_coordinate_count]{},
        transported[trace_rebase_tangent_rank]
                   [trace_rebase_coordinate_count]{};
    const bool differential = formed &&
        trace_rebase_differential_detail::gradient(
            fiber[0], fiber[1], out.predicted[step + 1U],
            target_gradient) &&
        trace_rebase_differential_detail::map_jacobian(
            maps[move], out.predicted[step], jacobian);
    trace_rebase_differential_detail::transport(jacobian, basis, transported);
    out.transported_rank[step] =
        trace_rebase_differential_detail::row_rank(transported);
    out.transport_exact[step] = differential &&
        out.transported_rank[step] == trace_rebase_tangent_rank &&
        trace_rebase_differential_detail::chain(target_gradient, transported);
    exact = exact && formed && out.transport_exact[step];
  }
  const auto first_move = static_cast<std::uint8_t>(card.moves[0]);
  auto ablated_map = maps[first_move];
  ablated_map.identity = {};
  std::int64_t ablated_target[trace_rebase_coordinate_count]{};
  out.map_exclusion = founded_predict(
                          ablated_map, out.predicted[0], ablated_target)
                          ? trace_rebase_obstruction::none
                          : trace_rebase_obstruction::map_organ_absent;
  auto missing_sum = fiber[0];
  auto missing_product = fiber[1];
  missing_sum.identity = {};
  missing_product.identity = {};
  std::int64_t ablated_gradient[trace_rebase_coordinate_count]{};
  const bool sum_continues = trace_rebase_differential_detail::gradient(
      missing_sum, fiber[1], out.predicted[0], ablated_gradient);
  const bool product_continues = trace_rebase_differential_detail::gradient(
      fiber[0], missing_product, out.predicted[0], ablated_gradient);
  out.lift_exclusion = !sum_continues && !product_continues
                           ? trace_rebase_obstruction::lift_organ_absent
                           : trace_rebase_obstruction::none;
  std::int64_t alternatives[trace_rebase_move_count]
                           [trace_rebase_coordinate_count]{};
  bool alternatives_exact = true, alternatives_differ = false;
  for (std::uint8_t move = 0; move < trace_rebase_move_count; ++move)
    alternatives_exact = alternatives_exact && founded_predict(
        maps[move], out.predicted[0], alternatives[move]);
  for (std::uint8_t move = 1; move < trace_rebase_move_count; ++move)
    for (std::uint8_t coordinate = 0;
         coordinate < trace_rebase_coordinate_count; ++coordinate)
      alternatives_differ = alternatives_differ ||
          alternatives[0][coordinate] != alternatives[move][coordinate];
  out.orientation_exclusion = alternatives_exact && alternatives_differ
      ? trace_rebase_obstruction::orientation_unresolved
      : trace_rebase_obstruction::none;
  out.aperture_control = out.path_length > trace_rebase_path_depth
      ? trace_rebase_obstruction::aperture_exceeded
      : trace_rebase_obstruction::none;
  exact_matrix2 foil[3]{card.seed[0], card.seed[1], card.seed[2]};
  foil[card.changed_matrix].value[card.changed_slot] = card.changed_value;
  out.determinant_control =
      trace_rebase_matrix_detail::valid(foil)
          ? trace_rebase_obstruction::none
          : trace_rebase_obstruction::unsupported_determinant;
  out.prediction_before_comparison = exact;
}
HOLONICS_CALLABLE inline void compare(
    const heldout_trace_rebase_source &source,
    heldout_trace_rebase_receipt &out) noexcept {
  if (!out.prediction_before_comparison || !source.valid)
    return;
  for (std::uint8_t step = 0; step <= out.path_length; ++step)
    for (std::uint8_t i = 0; i < trace_rebase_coordinate_count; ++i) {
      out.source[step][i] = source.coordinates[step][i];
      out.residuals = static_cast<std::uint16_t>(
          out.residuals +
          (out.predicted[step][i] != source.coordinates[step][i]));
    }
  out.compared = true;
  out.theory_formed = out.residuals == 0 &&
      out.map_exclusion == trace_rebase_obstruction::map_organ_absent &&
      out.lift_exclusion == trace_rebase_obstruction::lift_organ_absent &&
      out.orientation_exclusion == trace_rebase_obstruction::orientation_unresolved &&
      out.aperture_control == trace_rebase_obstruction::aperture_exceeded &&
      out.determinant_control == trace_rebase_obstruction::unsupported_determinant;
}

} // namespace holonics::organ::heldout_trace_rebase_detail
