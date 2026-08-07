#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::organ {
inline constexpr std::size_t phase_crystal_case_capacity = 16;
inline constexpr std::size_t phase_crystal_point_capacity = 19U * 19U;
inline constexpr std::size_t phase_crystal_series_capacity = 32;

enum class phase_case_kind : std::uint8_t {
  prime_pair,
  composite_coprime,
  composite_shared_factor,
  reversed_dominance,
  exact_dilation,
  exact_turn,
  reversed_pair
};

enum class phase_crystal_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  arithmetic_refused,
  cell_boundary_residual,
  orbit_partition_refused,
  shape_factorization_refused,
  hull_refused,
  series_refused,
  control_refused,
  continuation_refused,
  render_refused,
  checker_rejected,
  rest_refused
};

struct phase_ratio final {
  std::int64_t numerator{};
  std::uint64_t denominator{1};
};

struct phase_case_definition final {
  std::uint16_t first_modulus{};
  std::uint16_t second_modulus{};
  std::uint16_t scale_numerator{1};
  std::uint16_t scale_denominator{1};
  phase_case_kind kind{phase_case_kind::prime_pair};
  bool second_dominant{};
  bool rational_turn{};
};

struct phase_crystal_foundation final {
  exact::word ecology{};
  exact::word product_cells{};
  exact::word diagonal_transport{};
  exact::word receiver_projection{};
  exact::word series_current{};
  exact::word provenance{};
  exact::word case_seed{};
  std::uint16_t case_count{};
};

struct phase_crystal_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word material{};
};

struct phase_crystal_theory_plan final {
  exact::word passage{};
  exact::word diagonal_statement{};
  exact::word coprime_statement{};
  exact::word population_statement{};
  exact::word series_statement{};
  exact::word lineage{};
  bool diagonal_lcm{};
  bool coprime_full_tour{};
  bool cell_population_product{};
  bool seam_cancellation{};
  bool gauss_transport{};
  bool projection_distinguished{};
};

struct acquired_phase_crystal final {
  exact::word identity{};
  exact::word passage{};
  exact::word kernel_return{};
  exact::word lineage{};
  bool accepted{};
};

}  // namespace holonics::organ
