#pragma once

#include <holonics/codec/elementary_calculus_face.hpp>

namespace holonics::codec {

using trace_rebase_formal_face = elementary_formal_face;
using trace_rebase_dossier_face = elementary_dossier_face;
inline constexpr std::uint8_t trace_rebase_surface_moves = 5;
inline constexpr std::uint8_t trace_rebase_surface_coordinates = 7;
inline constexpr std::uint8_t trace_rebase_surface_features = 121;
struct trace_rebase_discovery_surface final {
  std::int64_t coefficients[trace_rebase_surface_moves]
                           [trace_rebase_surface_coordinates]
                           [trace_rebase_surface_features]{};
  std::uint8_t degrees[trace_rebase_surface_moves]
                      [trace_rebase_surface_coordinates]{};
  std::uint16_t transitions[trace_rebase_surface_moves][4]{};
  std::int64_t deck_vector[trace_rebase_surface_coordinates]{};
  std::int64_t deck_image[trace_rebase_surface_coordinates]{};
  std::int64_t deck_eigenvalue{};
  exact::word passage{};
  bool exact{};
};
struct trace_rebase_witness_surface final {
  std::int64_t deck_vector[trace_rebase_surface_coordinates]{};
  std::int64_t deck_image[trace_rebase_surface_coordinates]{};
  std::int64_t deck_eigenvalue{};
  std::int64_t fixed_matrices[3][4]{};
  std::int64_t fixed_chart[trace_rebase_surface_coordinates]{};
  std::int64_t exchange_matrices[3][4]{};
  std::int64_t exchange_target_matrices[3][4]{};
  std::int64_t exchange_chart[trace_rebase_surface_coordinates]{};
  std::int64_t exchange_target[trace_rebase_surface_coordinates]{};
  std::int64_t branch_matrices[3][4]{};
  std::int64_t branch_chart[trace_rebase_surface_coordinates]{};
  std::int64_t noncommutator[trace_rebase_surface_coordinates]{};
  std::int64_t chain_source_gradient[trace_rebase_surface_coordinates]{};
  std::int64_t chain_target_gradient[trace_rebase_surface_coordinates]{};
  std::int64_t chain_tangent[trace_rebase_surface_coordinates]{};
  std::int64_t chain_image[trace_rebase_surface_coordinates]{};
  std::int64_t chain_jacobian[trace_rebase_surface_coordinates]
                             [trace_rebase_surface_coordinates]{};
  exact::word passage{};
  bool exact{};
};
struct heldout_trace_rebase_surface final {
  std::int64_t predicted[13][trace_rebase_surface_coordinates]{};
  std::int64_t source[13][trace_rebase_surface_coordinates]{};
  std::uint8_t tangent_rank[13]{};
  std::uint8_t vertical_rank[13]{};
  bool branch[13]{};
  std::uint8_t moves[12]{};
  std::uint8_t path_length{};
  exact::word passage{};
  bool prediction_before_comparison{};
  bool exact{};
};

} // namespace holonics::codec
