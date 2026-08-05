#pragma once

#include <holonics/organ/trace_rebase_control_law.hpp>
#include <holonics/organ/trace_rebase_differential_law.hpp>
#include <holonics/organ/trace_rebase_joint_discovery_law.hpp>

namespace holonics::organ::trace_rebase_close_detail {

[[nodiscard]] HOLONICS_CALLABLE inline bool map_predict(
    const trace_rebase_map_organ &map, const std::int64_t *source,
    std::int64_t (&target)[trace_rebase_coordinate_count]) noexcept {
  if (!map.primitive)
    return false;
  bool exact = true;
  for (std::uint8_t i = 0; i < trace_rebase_coordinate_count; ++i)
    exact = exact && trace_rebase_discovery_detail::predict(
                         map.coefficients[i], source, target[i]);
  return exact;
}
HOLONICS_CALLABLE inline bool differentiate(
    const trace_fiber_organ (&fiber)[2],
    trace_rebase_discovery_receipt &out) noexcept {
  bool exact = true;
  for (std::uint16_t i = 0; i < out.edge_count; ++i) {
    auto &edge = out.edges[i];
    const auto &state = out.states[edge.state];
    const auto &map = out.maps[static_cast<std::uint8_t>(edge.move)];
    std::int64_t predicted[trace_rebase_coordinate_count]{};
    bool local = map_predict(map, state.coordinates, predicted);
    for (std::uint8_t j = 0; j < trace_rebase_coordinate_count; ++j)
      local = local && predicted[j] == edge.target[j];
    if (static_cast<std::uint8_t>(edge.move) == 0U) {
      local = local && trace_rebase_differential_detail::gradient(
                           fiber[0], fiber[1], state.coordinates,
                           edge.source_gradient);
      edge.source_tangent_rank = trace_rebase_differential_detail::tangent(
          edge.source_gradient, edge.tangent);
    } else {
      const auto &first = out.edges[edge.state * trace_rebase_move_count];
      edge.source_tangent_rank = first.source_tangent_rank;
      for (std::uint8_t column = 0; column < trace_rebase_coordinate_count;
           ++column)
        edge.source_gradient[column] = first.source_gradient[column];
      for (std::uint8_t row = 0; row < trace_rebase_tangent_rank; ++row)
        for (std::uint8_t column = 0; column < trace_rebase_coordinate_count;
             ++column)
          edge.tangent[row][column] = first.tangent[row][column];
    }
    local = local && trace_rebase_differential_detail::gradient(
                         fiber[0], fiber[1], edge.target,
                         edge.target_gradient) &&
            trace_rebase_differential_detail::map_jacobian(
                         map, state.coordinates, edge.jacobian);
    std::int64_t target_basis[trace_rebase_tangent_rank]
                             [trace_rebase_coordinate_count]{};
    edge.target_tangent_rank = trace_rebase_differential_detail::tangent(
        edge.target_gradient, target_basis);
    trace_rebase_differential_detail::transport(edge.jacobian, edge.tangent,
                                                edge.transported);
    edge.transported_rank =
        trace_rebase_differential_detail::row_rank(edge.transported);
    edge.source_vertical_rank = edge.source_gradient[6] == 0 ? 1U : 0U;
    edge.target_vertical_rank = edge.target_gradient[6] == 0 ? 1U : 0U;
    const bool smooth =
        edge.source_tangent_rank == trace_rebase_tangent_rank &&
        edge.target_tangent_rank == trace_rebase_tangent_rank;
    const bool singular = edge.source_tangent_rank == 0 ||
                          edge.target_tangent_rank == 0;
    edge.differential_obstruction = singular
        ? trace_rebase_obstruction::singular_hypersurface
        : trace_rebase_obstruction::none;
    edge.chain_exact = local && smooth &&
        trace_rebase_differential_detail::chain(edge.target_gradient,
                                                edge.transported) &&
        edge.transported_rank == trace_rebase_tangent_rank &&
        edge.source_vertical_rank == (edge.source_branch ? 1U : 0U) &&
        edge.target_vertical_rank == (edge.target_branch ? 1U : 0U);
    const bool differential_exact = edge.chain_exact || (local && singular);
    if (singular)
      ++out.singular_edges;
    if (!differential_exact)
      ++out.tangent_failures;
    const auto move = static_cast<std::uint8_t>(edge.move);
    auto &count = out.transitions[move];
    auto &source_count = out.source_transitions[move][state.source];
    if (!edge.source_branch && !edge.target_branch)
      ++count.regular_regular, ++source_count.regular_regular;
    else if (!edge.source_branch && edge.target_branch)
      ++count.regular_branch, ++source_count.regular_branch;
    else if (edge.source_branch && !edge.target_branch)
      ++count.branch_regular, ++source_count.branch_regular;
    else
      ++count.branch_branch, ++source_count.branch_branch;
    exact = exact && differential_exact;
  }
  return exact;
}
HOLONICS_CALLABLE inline bool generator_controls(
    const trace_rebase_discovery_receipt &out) noexcept {
  bool exact = true;
  for (std::uint16_t i = 0; i < out.state_count; ++i) {
    constexpr std::uint8_t first[5]{0, 1, 2, 3, 4};
    constexpr std::uint8_t second[5]{0, 1, 2, 4, 3};
    for (std::uint8_t relation = 0; relation < 5; ++relation) {
      std::int64_t middle[trace_rebase_coordinate_count]{};
      std::int64_t returned[trace_rebase_coordinate_count]{};
      exact = exact && map_predict(out.maps[first[relation]],
                                   out.states[i].coordinates, middle) &&
              map_predict(out.maps[second[relation]], middle, returned);
      for (std::uint8_t j = 0; j < trace_rebase_coordinate_count; ++j)
        exact = exact && returned[j] == out.states[i].coordinates[j];
    }
  }
  return exact;
}
HOLONICS_CALLABLE inline void apply_jacobian(
    const std::int64_t jacobian[trace_rebase_coordinate_count]
                               [trace_rebase_coordinate_count],
    const std::int64_t *source,
    std::int64_t (&target)[trace_rebase_coordinate_count]) noexcept {
  for (std::uint8_t row = 0; row < trace_rebase_coordinate_count; ++row)
    for (std::uint8_t column = 0; column < trace_rebase_coordinate_count;
         ++column)
      target[row] += jacobian[row][column] * source[column];
}
HOLONICS_CALLABLE inline void retain_witnesses(
    const trace_fiber_organ (&fiber)[2],
    trace_rebase_discovery_receipt &out) noexcept {
  out.witnesses[0].kind = 0;
  out.witnesses[0].found = generator_controls(out);
  for (std::uint16_t i = 0; i < out.state_count; ++i) {
    if (!out.witnesses[1].found) {
      std::int64_t first[trace_rebase_coordinate_count]{},
          second[trace_rebase_coordinate_count]{}, left[trace_rebase_coordinate_count]{},
          right[trace_rebase_coordinate_count]{};
      const bool formed = map_predict(out.maps[0], out.states[i].coordinates, first) &&
          map_predict(out.maps[1], first, left) &&
          map_predict(out.maps[1], out.states[i].coordinates, second) &&
          map_predict(out.maps[0], second, right);
      bool different = false, tangent_different = false;
      for (std::uint8_t j = 0; j < trace_rebase_coordinate_count; ++j) {
        out.witnesses[1].vector[j] = left[j] - right[j];
        different = different || left[j] != right[j];
      }
      std::int64_t j0[trace_rebase_coordinate_count]
                         [trace_rebase_coordinate_count]{},
          j1[trace_rebase_coordinate_count][trace_rebase_coordinate_count]{},
          j01[trace_rebase_coordinate_count][trace_rebase_coordinate_count]{},
          j10[trace_rebase_coordinate_count][trace_rebase_coordinate_count]{};
      bool tangent_exact = formed &&
          trace_rebase_differential_detail::map_jacobian(out.maps[0],
                                                         out.states[i].coordinates,
                                                         j0) &&
          trace_rebase_differential_detail::map_jacobian(out.maps[1],
                                                         out.states[i].coordinates,
                                                         j1) &&
          trace_rebase_differential_detail::map_jacobian(out.maps[1], first,
                                                         j01) &&
          trace_rebase_differential_detail::map_jacobian(out.maps[0], second,
                                                         j10);
      std::int64_t along0[trace_rebase_coordinate_count]{},
          along1[trace_rebase_coordinate_count]{},
          tangent_left[trace_rebase_coordinate_count]{},
          tangent_right[trace_rebase_coordinate_count]{};
      const auto &basis = out.edges[i * trace_rebase_move_count].tangent[0];
      apply_jacobian(j0, basis, along0);
      apply_jacobian(j1, basis, along1);
      apply_jacobian(j01, along0, tangent_left);
      apply_jacobian(j10, along1, tangent_right);
      for (std::uint8_t j = 0; j < trace_rebase_coordinate_count; ++j) {
        out.witnesses[1].image[j] = tangent_left[j] - tangent_right[j];
        tangent_different = tangent_different ||
                            tangent_left[j] != tangent_right[j];
      }
      out.witnesses[1].kind = 1;
      out.witnesses[1].first = i;
      out.witnesses[1].found = tangent_exact && different && tangent_different;
    }
    if (!out.witnesses[3].found && out.states[i].branch) {
      static_cast<void>(trace_rebase_differential_detail::deck_vertical(
          fiber, out.states[i], out.witnesses[3]));
    }
    if (!out.witnesses[6].found) {
      const auto edge0 = static_cast<std::uint16_t>(i * trace_rebase_move_count);
      const auto edge1 = static_cast<std::uint16_t>(edge0 + 1U);
      bool different = false;
      for (std::uint8_t j = 0; j < trace_rebase_coordinate_count; ++j) {
        out.witnesses[6].vector[j] =
            out.edges[edge0].target[j] - out.edges[edge1].target[j];
        different = different || out.witnesses[6].vector[j] != 0;
      }
      out.witnesses[6].kind = 6;
      out.witnesses[6].first = edge0;
      out.witnesses[6].second = edge1;
      out.witnesses[6].found = different;
    }
  }
  const auto source_stride = static_cast<std::uint16_t>(
      trace_rebase_seed_count * trace_rebase_states_per_seed);
  for (std::uint16_t i = 0; i < source_stride && !out.witnesses[2].found; ++i) {
    const auto j = static_cast<std::uint16_t>(2U * source_stride + i);
    bool same = true, changed = false;
    for (std::uint8_t k = 0; k < trace_rebase_coordinate_count; ++k)
      same = same && out.states[i].coordinates[k] == out.states[j].coordinates[k];
    for (std::uint8_t m = 0; m < 3; ++m)
      changed = changed || !elementary_matrix_detail::equal(
          out.states[i].matrices[m], out.states[j].matrices[m]);
    if (same && changed)
      out.witnesses[2] = {i, j, {}, {}, 0, 2, true};
  }
  for (std::uint16_t i = 0; i < out.edge_count; ++i) {
    if (!out.witnesses[4].found && out.edges[i].source_branch &&
        !out.edges[i].target_branch)
      out.witnesses[4] = {i, i, {}, {}, 0, 4, true};
    if (!out.witnesses[5].found && !out.edges[i].source_branch &&
        out.edges[i].target_branch)
      out.witnesses[5] = {i, i, {}, {}, 0, 5, true};
  }
  out.witnesses_complete = true;
  for (const auto &witness : out.witnesses)
    out.witnesses_complete = out.witnesses_complete && witness.found;
}
HOLONICS_CALLABLE inline void close(
    const trace_fiber_organ (&fiber)[2], trace_rebase_discovery_receipt &out,
    trace_rebase_workspace &workspace) noexcept {
  const bool maps = trace_rebase_joint_detail::discover_maps(out, workspace);
  const bool source_exact = maps &&
      trace_rebase_control_detail::source_holdouts(out, workspace);
  const bool aperture_exact = source_exact &&
      trace_rebase_control_detail::aperture_controls(out, workspace);
  const bool tangent_exact = aperture_exact && differentiate(fiber, out);
  retain_witnesses(fiber, out);
  out.population_complete = out.state_count == trace_rebase_state_capacity &&
      out.edge_count == trace_rebase_edge_capacity;
  out.controls_complete = aperture_exact && generator_controls(out);
  out.theory_formed = out.source_ports_distinct && out.population_complete &&
      out.controls_complete && out.witnesses_complete && tangent_exact &&
      out.residuals == 0 && out.tangent_failures == 0;
}
} // namespace holonics::organ::trace_rebase_close_detail
