#pragma once

#include <holonics/codec/trace_rebase_face.hpp>
#include <holonics/event/trace_rebase_rest.hpp>

namespace holonics::event {

HOLONICS_CALLABLE inline void copy_formal_matrix(
    const organ::exact_matrix2 &source, std::int64_t (&target)[4]) noexcept {
  for (std::uint8_t i = 0; i < 4; ++i)
    target[i] = source.value[i];
}

[[nodiscard]] HOLONICS_CALLABLE inline codec::trace_rebase_discovery_surface
trace_rebase_surface(const organ::trace_rebase_discovery_receipt &source) noexcept {
  codec::trace_rebase_discovery_surface out{};
  for (std::uint8_t move = 0; move < organ::trace_rebase_move_count; ++move) {
    for (std::uint8_t target = 0; target < organ::trace_rebase_coordinate_count;
         ++target) {
      out.degrees[move][target] = source.maps[move].degrees[target];
      for (std::uint8_t i = 0; i < organ::trace_rebase_feature_count; ++i)
        out.coefficients[move][target][i] =
            source.maps[move].coefficients[target][i];
    }
    out.transitions[move][0] = source.transitions[move].regular_regular;
    out.transitions[move][1] = source.transitions[move].regular_branch;
    out.transitions[move][2] = source.transitions[move].branch_regular;
    out.transitions[move][3] = source.transitions[move].branch_branch;
  }
  for (std::uint8_t i = 0; i < organ::trace_rebase_coordinate_count; ++i) {
    out.deck_vector[i] = source.witnesses[3].vector[i];
    out.deck_image[i] = source.witnesses[3].image[i];
  }
  out.deck_eigenvalue = source.witnesses[3].eigenvalue;
  out.passage = source.passage;
  out.exact = source.theory_formed;
  return out;
}
[[nodiscard]] HOLONICS_CALLABLE inline codec::trace_rebase_witness_surface
trace_rebase_witness_surface(
    const organ::trace_rebase_discovery_receipt &source) noexcept {
  codec::trace_rebase_witness_surface out{};
  for (std::uint8_t i = 0; i < organ::trace_rebase_coordinate_count; ++i) {
    out.deck_vector[i] = source.witnesses[3].vector[i];
    out.deck_image[i] = source.witnesses[3].image[i];
  }
  out.deck_eigenvalue = source.witnesses[3].eigenvalue;
  std::uint16_t fixed = 0;
  for (std::uint16_t state = 0; state < source.state_count; ++state) {
    bool chart_fixed = true;
    for (std::uint8_t move = 0; move < organ::trace_rebase_move_count; ++move)
      for (std::uint8_t coordinate = 0;
           coordinate < organ::trace_rebase_coordinate_count; ++coordinate)
        chart_fixed = chart_fixed &&
            source.edges[state * organ::trace_rebase_move_count + move]
                    .target[coordinate] == source.states[state].coordinates[coordinate];
    if (chart_fixed) {
      fixed = state;
      break;
    }
  }
  const auto exchange_edge = source.witnesses[6].first;
  const auto exchange = source.edges[exchange_edge].state;
  const auto branch = source.witnesses[3].first;
  const auto chain_edge = static_cast<std::uint16_t>(
      source.witnesses[1].first * organ::trace_rebase_move_count);
  for (std::uint8_t matrix = 0; matrix < 3; ++matrix) {
    copy_formal_matrix(source.states[fixed].matrices[matrix],
                       out.fixed_matrices[matrix]);
    copy_formal_matrix(source.states[exchange].matrices[matrix],
                       out.exchange_matrices[matrix]);
    copy_formal_matrix(source.edges[exchange_edge].target_matrices[matrix],
                       out.exchange_target_matrices[matrix]);
    copy_formal_matrix(source.states[branch].matrices[matrix],
                       out.branch_matrices[matrix]);
  }
  for (std::uint8_t i = 0; i < organ::trace_rebase_coordinate_count; ++i) {
    out.fixed_chart[i] = source.states[fixed].coordinates[i];
    out.exchange_chart[i] = source.states[exchange].coordinates[i];
    out.exchange_target[i] = source.edges[exchange_edge].target[i];
    out.branch_chart[i] = source.states[branch].coordinates[i];
    out.noncommutator[i] = source.witnesses[1].vector[i];
    out.chain_source_gradient[i] = source.edges[chain_edge].source_gradient[i];
    out.chain_target_gradient[i] = source.edges[chain_edge].target_gradient[i];
    out.chain_tangent[i] = source.edges[chain_edge].tangent[0][i];
    out.chain_image[i] = source.edges[chain_edge].transported[0][i];
    for (std::uint8_t j = 0; j < organ::trace_rebase_coordinate_count; ++j)
      out.chain_jacobian[i][j] = source.edges[chain_edge].jacobian[i][j];
  }
  out.passage = source.passage;
  out.exact = source.theory_formed && source.witnesses_complete &&
              source.edges[chain_edge].chain_exact;
  return out;
}
[[nodiscard]] HOLONICS_CALLABLE inline codec::trace_rebase_discovery_surface
rested_trace_rebase_surface(const trace_rebase_law_bundle &source) noexcept {
  codec::trace_rebase_discovery_surface out{};
  for (std::uint8_t move = 0; move < organ::trace_rebase_move_count; ++move) {
    for (std::uint8_t target = 0; target < organ::trace_rebase_coordinate_count;
         ++target) {
      out.degrees[move][target] = source.maps[move].degrees[target];
      for (std::uint8_t i = 0; i < organ::trace_rebase_feature_count; ++i)
        out.coefficients[move][target][i] =
            source.maps[move].coefficients[target][i];
    }
    out.transitions[move][0] = source.transitions[move].regular_regular;
    out.transitions[move][1] = source.transitions[move].regular_branch;
    out.transitions[move][2] = source.transitions[move].branch_regular;
    out.transitions[move][3] = source.transitions[move].branch_branch;
  }
  for (std::uint8_t i = 0; i < organ::trace_rebase_coordinate_count; ++i) {
    out.deck_vector[i] = source.deck.vector[i];
    out.deck_image[i] = source.deck.image[i];
  }
  out.deck_eigenvalue = source.deck.eigenvalue;
  out.passage = source.discovery.passage;
  out.exact = source.checker_founded && source.tangent.accepted &&
              source.deck.return_receipt.accepted && source.deck.primitive;
  return out;
}
[[nodiscard]] HOLONICS_CALLABLE inline codec::heldout_trace_rebase_surface
heldout_trace_rebase_surface(
    const organ::heldout_trace_rebase_receipt &source) noexcept {
  codec::heldout_trace_rebase_surface out{};
  out.path_length = source.path_length;
  for (std::uint8_t step = 0; step < source.path_length; ++step)
    out.moves[step] = static_cast<std::uint8_t>(source.moves[step]);
  for (std::uint8_t step = 0; step <= source.path_length; ++step) {
    for (std::uint8_t i = 0; i < organ::trace_rebase_coordinate_count; ++i) {
      out.predicted[step][i] = source.predicted[step][i];
      out.source[step][i] = source.source[step][i];
    }
    out.tangent_rank[step] = source.tangent_rank[step];
    out.vertical_rank[step] = source.vertical_rank[step];
    out.branch[step] = source.branch[step];
  }
  out.passage = source.passage;
  out.prediction_before_comparison = source.prediction_before_comparison;
  out.exact = source.theory_formed;
  return out;
}

} // namespace holonics::event
