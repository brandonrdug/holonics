#pragma once

#include <holonics/organ/trace_rebase_discovery_law.hpp>

namespace holonics::organ::trace_rebase_control_detail {

[[nodiscard]] HOLONICS_CALLABLE inline bool source_holdouts(
    trace_rebase_discovery_receipt &out,
    trace_rebase_workspace &workspace) noexcept {
  bool exact = true;
  for (std::uint8_t excluded = 0; excluded < trace_rebase_source_count;
       ++excluded) {
    for (std::uint8_t degree = 0; degree <= 3; ++degree) {
      trace_rebase_feature_detail::reset(workspace.basis);
      const auto columns = trace_rebase_feature_detail::monomial_count(degree);
      for (std::uint16_t state = 0; state < out.state_count &&
                                    workspace.basis.rank < columns;
           ++state) {
        if (out.states[state].source == excluded)
          continue;
        std::int64_t values[trace_rebase_monomial_count]{};
        trace_rebase_feature_detail::monomials(out.states[state].coordinates,
                                               values);
        trace_rebase_feature_detail::insert_values(workspace.basis, values,
                                                   columns);
      }
      out.source_holdout_ranks[excluded][degree] = workspace.basis.rank;
      exact = exact && workspace.basis.exact &&
              workspace.basis.rank == columns;
    }
    for (std::uint8_t move = 0; move < trace_rebase_move_count; ++move)
      for (std::uint8_t target = 0; target < trace_rebase_coordinate_count;
           ++target)
        for (std::uint16_t state = 0; state < out.state_count; ++state) {
          if (out.states[state].source != excluded)
            continue;
          const auto edge = static_cast<std::uint16_t>(
              state * trace_rebase_move_count + move);
          out.source_holdout_residuals[move][excluded] =
              static_cast<std::uint16_t>(
                  out.source_holdout_residuals[move][excluded] +
                  (trace_rebase_discovery_detail::residual(
                       out.maps[move].coefficients[target],
                       out.states[state].coordinates,
                       out.edges[edge].target[target]) != 0));
        }
  }
  for (const auto &by_move : out.source_holdout_residuals)
    for (const auto residual : by_move)
      exact = exact && residual == 0;
  return exact;
}
HOLONICS_CALLABLE inline void control_row(
    const trace_rebase_discovery_receipt &out, std::uint16_t state,
    std::uint8_t deleted, bool target_present,
    std::int64_t (&values)[trace_rebase_feature_count],
    std::uint8_t &columns) noexcept {
  std::int64_t monomials[trace_rebase_monomial_count]{};
  trace_rebase_feature_detail::monomials(out.states[state].coordinates,
                                         monomials);
  columns = 0;
  for (std::uint8_t i = 0; i < trace_rebase_monomial_count; ++i) {
    std::uint8_t powers[trace_rebase_coordinate_count]{};
    trace_rebase_feature_detail::exponents(i, powers);
    if (deleted >= trace_rebase_coordinate_count || powers[deleted] == 0)
      values[columns++] = monomials[i];
  }
  if (target_present) {
    const auto edge = static_cast<std::uint16_t>(
        state * trace_rebase_move_count + out.control_move);
    values[columns++] = out.edges[edge].target[out.control_target];
  }
}
[[nodiscard]] HOLONICS_CALLABLE inline bool aperture_controls(
    trace_rebase_discovery_receipt &out,
    trace_rebase_workspace &workspace) noexcept {
  out.control_move = 0;
  out.control_target = 6;
  trace_rebase_candidate degree_two{};
  const bool degree_two_found =
      trace_rebase_discovery_detail::discover_filtered(
          out, trace_rebase_move::swap12, out.control_target, workspace,
          degree_two, 255U, 2U);
  out.degree_two_rank = degree_two.rank;
  out.degree_two_obstruction = degree_two.obstruction;
  bool exact = !degree_two_found &&
               degree_two.obstruction != trace_rebase_obstruction::none;
  for (std::uint8_t deleted = 0; deleted < trace_rebase_coordinate_count;
       ++deleted) {
    trace_rebase_feature_detail::reset(workspace.basis);
    std::uint8_t columns = 0;
    for (std::uint16_t state = 0; state < out.state_count; ++state) {
      std::int64_t values[trace_rebase_feature_count]{};
      control_row(out, state, deleted, true, values, columns);
      if (workspace.basis.rank < columns)
        trace_rebase_feature_detail::insert_values(workspace.basis, values,
                                                   columns);
    }
    out.coordinate_deleted_rank[deleted] = workspace.basis.rank;
    out.coordinate_deleted_features[deleted] = columns;
    exact = exact && workspace.basis.exact &&
            workspace.basis.rank == columns;
  }
  trace_rebase_feature_detail::reset(workspace.basis);
  std::uint8_t target_deleted_columns = 0;
  for (std::uint16_t state = 0; state < out.state_count; ++state) {
    std::int64_t values[trace_rebase_feature_count]{};
    control_row(out, state, 255U, false, values, target_deleted_columns);
    if (workspace.basis.rank < target_deleted_columns)
      trace_rebase_feature_detail::insert_values(
          workspace.basis, values, target_deleted_columns);
  }
  out.target_deleted_rank = workspace.basis.rank;
  exact = exact && workspace.basis.exact &&
          workspace.basis.rank == target_deleted_columns;
  trace_rebase_feature_detail::reset(workspace.basis);
  for (std::uint16_t state = 0;
       state < static_cast<std::uint16_t>(trace_rebase_feature_count - 2U);
       ++state) {
    std::int64_t values[trace_rebase_feature_count]{};
    std::uint8_t columns = 0;
    control_row(out, state, 255U, true, values, columns);
    trace_rebase_feature_detail::insert_values(workspace.basis, values,
                                               columns);
  }
  out.row_deficient_rank = workspace.basis.rank;
  exact = exact && workspace.basis.exact &&
          workspace.basis.rank < trace_rebase_monomial_count;
  out.coefficient_height_limit = trace_rebase_coefficient_height_limit;
  std::uint64_t height = 0;
  for (const auto &map : out.maps)
    for (const auto &target : map.coefficients)
      for (const auto coefficient : target) {
        const auto absolute = static_cast<std::uint64_t>(
            exact::small_rational_law::absolute(coefficient));
        if (absolute > height)
          height = absolute;
      }
  out.coefficient_height = height <= 65'535U
                               ? static_cast<std::uint16_t>(height)
                               : 65'535U;
  exact = exact && height <= out.coefficient_height_limit;
  return exact;
}

} // namespace holonics::organ::trace_rebase_control_detail
