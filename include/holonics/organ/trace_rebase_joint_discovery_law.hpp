#pragma once

#include <holonics/organ/trace_rebase_discovery_law.hpp>

namespace holonics::organ::trace_rebase_joint_detail {

HOLONICS_CALLABLE inline void row(
    const trace_rebase_discovery_receipt &out, std::uint16_t state,
    std::uint8_t degree,
    std::int64_t (&values)[trace_rebase_joint_column_count]) noexcept {
  std::int64_t monomials[trace_rebase_monomial_count]{};
  trace_rebase_feature_detail::monomials(out.states[state].coordinates,
                                         monomials);
  const auto features = trace_rebase_feature_detail::monomial_count(degree);
  for (std::uint8_t i = 0; i < features; ++i)
    values[i] = monomials[i];
  for (std::uint8_t move = 0; move < trace_rebase_move_count; ++move) {
    const auto edge = static_cast<std::uint16_t>(
        state * trace_rebase_move_count + move);
    for (std::uint8_t target = 0; target < trace_rebase_coordinate_count;
         ++target)
      values[features + move * trace_rebase_coordinate_count + target] =
          out.edges[edge].target[target];
  }
}
HOLONICS_CALLABLE inline void candidate(
    const trace_rebase_basis &basis, std::uint8_t degree,
    std::uint8_t move, std::uint8_t target,
    trace_rebase_candidate &out) noexcept {
  out = {};
  const auto monomials = trace_rebase_feature_detail::monomial_count(degree);
  const auto column = static_cast<std::uint8_t>(
      monomials + move * trace_rebase_coordinate_count + target);
  out.rows = trace_rebase_state_capacity;
  out.degree = degree;
  out.features = static_cast<std::uint8_t>(monomials + 1U);
  out.rank = monomials;
  out.nullity = 1;
  out.move = static_cast<trace_rebase_move>(move);
  out.target = target;
  for (std::uint8_t row = 0; row < basis.rank; ++row) {
    auto coefficient = basis.rows[row][column];
    if (coefficient > trace_rebase_rank_modulus / 2)
      coefficient -= trace_rebase_rank_modulus;
    out.coefficients[basis.pivots[row]] = -coefficient;
  }
  out.coefficients[trace_rebase_monomial_count] = 1;
  out.obstruction = trace_rebase_obstruction::none;
  out.primitive = true;
}
[[nodiscard]] HOLONICS_CALLABLE inline bool discover_maps(
    trace_rebase_discovery_receipt &out,
    trace_rebase_workspace &workspace) noexcept {
  bool selected[trace_rebase_map_count]{};
  std::uint8_t selected_count = 0;
  for (std::uint8_t degree = 0; degree <= 3; ++degree) {
    trace_rebase_feature_detail::reset(workspace.basis);
    const auto features = trace_rebase_feature_detail::monomial_count(degree);
    const auto columns = static_cast<std::uint8_t>(
        features + trace_rebase_map_count);
    for (std::uint16_t state = 0; state < out.state_count &&
                                  workspace.basis.rank < features;
         ++state) {
      std::int64_t values[trace_rebase_joint_column_count]{};
      row(out, state, degree, values);
      trace_rebase_feature_detail::insert_joint(
          workspace.basis, values, features, columns);
    }
    if (workspace.basis.rank != features)
      continue;
    for (std::uint8_t move = 0; move < trace_rebase_move_count; ++move)
      for (std::uint8_t target = 0; target < trace_rebase_coordinate_count;
           ++target) {
        const auto index = static_cast<std::uint8_t>(
            move * trace_rebase_coordinate_count + target);
        if (selected[index])
          continue;
        auto &result = out.candidates[index];
        candidate(workspace.basis, degree, move, target, result);
        bool exact = true;
        for (std::uint16_t state = 0; state < out.state_count; ++state) {
          const auto edge = static_cast<std::uint16_t>(
              state * trace_rebase_move_count + move);
          exact = exact && trace_rebase_discovery_detail::residual(
                               result.coefficients,
                               out.states[state].coordinates,
                               out.edges[edge].target[target]) == 0;
        }
        result.selected = exact;
        result.obstruction = exact ? trace_rebase_obstruction::none
                                   : trace_rebase_obstruction::residual;
        if (exact) {
          ++selected_count;
          selected[index] = true;
        }
      }
  }
  for (std::uint8_t move = 0; move < trace_rebase_move_count; ++move) {
    auto &map = out.maps[move];
    map.move = static_cast<trace_rebase_move>(move);
    map.lineage = out.lineage;
    map.primitive = true;
    for (std::uint8_t target = 0; target < trace_rebase_coordinate_count;
         ++target) {
      const auto &source = out.candidates[
          move * trace_rebase_coordinate_count + target];
      map.degrees[target] = source.degree;
      map.primitive = map.primitive && source.selected && source.primitive;
      for (std::uint8_t i = 0; i < trace_rebase_feature_count; ++i)
        map.coefficients[target][i] = source.coefficients[i];
    }
  }
  return selected_count == trace_rebase_map_count;
}

} // namespace holonics::organ::trace_rebase_joint_detail
