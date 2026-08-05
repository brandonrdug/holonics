#pragma once

#include <cstdint>

#include <holonics/organ/trace_fiber_schema.hpp>

namespace holonics::organ {

inline constexpr std::uint8_t trace_rebase_source_count = 3;
inline constexpr std::uint8_t trace_rebase_seed_count = 4;
inline constexpr std::uint8_t trace_rebase_move_count = 5;
inline constexpr std::uint8_t trace_rebase_coordinate_count = 7;
inline constexpr std::uint8_t trace_rebase_path_depth = 3;
inline constexpr std::uint16_t trace_rebase_states_per_seed = 106;
inline constexpr std::uint16_t trace_rebase_state_capacity = 1'272;
inline constexpr std::uint16_t trace_rebase_edge_capacity = 6'360;
inline constexpr std::uint8_t trace_rebase_monomial_count = 120;
inline constexpr std::uint8_t trace_rebase_feature_count = 121;
inline constexpr std::uint8_t trace_rebase_map_count = 35;
inline constexpr std::uint8_t trace_rebase_joint_column_count = 155;
inline constexpr std::uint8_t trace_rebase_tangent_rank = 6;
inline constexpr std::uint8_t trace_rebase_witness_count = 7;
inline constexpr std::uint8_t trace_rebase_heldout_path_capacity = 12;
inline constexpr std::uint16_t trace_rebase_coefficient_height_limit = 64;
inline constexpr std::int64_t trace_rebase_rank_modulus = 1'000'003;

enum class trace_rebase_move : std::uint8_t {
  swap12,
  swap23,
  invert1,
  shear12_positive,
  shear12_negative
};
enum class trace_rebase_obstruction : std::uint8_t {
  none,
  invalid_source,
  invalid_exact_row,
  full_rank,
  nonunique_kernel,
  insufficient_rows,
  residual,
  coefficient_height,
  map_organ_absent,
  lift_organ_absent,
  orientation_unresolved,
  aperture_exceeded,
  unsupported_determinant,
  singular_hypersurface,
  tangent_transport_failed,
  witness_absent,
  comparison_residual
};
struct trace_rebase_source_card final {
  cultivation_card_metadata metadata{};
  exact_matrix2 seeds[trace_rebase_seed_count][3]{};
};
struct trace_rebase_development_bundle final {
  trace_rebase_source_card sources[trace_rebase_source_count]{};
};
struct heldout_trace_rebase_card final {
  cultivation_card_metadata metadata{};
  exact_matrix2 seed[3]{};
  trace_rebase_move moves[trace_rebase_heldout_path_capacity]{};
  std::uint8_t path_length{};
  std::uint8_t changed_matrix{};
  std::uint8_t changed_slot{};
  std::int64_t changed_value{};
};

} // namespace holonics::organ
