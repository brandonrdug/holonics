#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::organ {

inline constexpr std::size_t expression_presentation_capacity = 3;
inline constexpr std::size_t expression_term_capacity = 12;
inline constexpr std::size_t expression_parameter_capacity = 21;
inline constexpr std::size_t expression_sample_capacity = 11;
inline constexpr std::size_t expression_series_capacity = 11;
inline constexpr std::size_t expression_basis_rank = 4;
inline constexpr std::size_t expression_x_capacity = 6;
inline constexpr std::size_t expression_reduction_capacity = 16;
inline constexpr std::size_t expression_residue_degree = 5;

struct sparse_expression_term final {
  std::int64_t coefficient{};
  std::uint8_t parameter_power{};
  std::uint8_t x_power{};
  std::uint8_t y_power{};
};

struct sparse_expression final {
  exact::word identity{};
  exact::word lineage{};
  sparse_expression_term terms[expression_term_capacity]{};
  std::uint8_t term_count{};
  bool exact{};
};

struct expression_affine_coefficient final {
  std::int64_t constant{};
  std::int64_t parameter{};
};

struct expression_x_polynomial final {
  expression_affine_coefficient coefficients[expression_x_capacity]{};
  std::uint8_t degree{};
  bool exact{};
};

struct expression_geometry_card final {
  exact::word schema{};
  exact::word occurrence{};
  exact::word lineage{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  std::uint32_t byte_count{};
  sparse_expression presentations[expression_presentation_capacity]{};
  std::int8_t discovery_min{};
  std::int8_t discovery_max{};
  std::int8_t holdout_first{};
  std::int8_t holdout_second{};
  std::int8_t chart_min{};
  std::int8_t chart_max{};
  std::uint8_t series_depth{};
  std::uint8_t presentation_count{};
  bool parsed{};
};

struct expression_geometry_foundation final {
  exact::word ecology{};
  exact::word expression{};
  exact::word ideal{};
  exact::word local_ring{};
  exact::word differential{};
  exact::word characteristic{};
  exact::word theorem{};
  exact::word provenance{};
  expression_geometry_card card{};
};

struct expression_geometry_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word material{};
};

enum class expression_geometry_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  expression_refused,
  ideal_refused,
  resultant_refused,
  local_ring_refused,
  differential_refused,
  scalar_refused,
  residue_refused,
  rechart_refused,
  control_refused,
  continuation_refused,
  render_refused,
  checker_rejected,
  rest_refused
};

struct expression_geometry_plan final {
  exact::word passage{};
  exact::word statement{};
  exact::word lineage{};
  std::uint16_t source_mask{};
  bool expressions_exact{};
  bool ideals_exact{};
  bool differential_exact{};
  bool characteristic_exact{};
  bool fibers_exact{};
};

struct acquired_expression_geometry final {
  exact::word identity{};
  exact::word passage{};
  exact::word kernel_return{};
  exact::word lineage{};
  exact::word morphology_delta{};
  bool accepted{};
};

}  // namespace holonics::organ
