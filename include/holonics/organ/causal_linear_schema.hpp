#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>
#include <holonics/organ/algebraic_variation_schema.hpp>
#include <holonics/organ/cm_incidence_schema.hpp>
#include <holonics/organ/toric_cycle_schema.hpp>

namespace holonics::organ {

inline constexpr std::size_t causal_matrix_rows = 16;
inline constexpr std::size_t causal_matrix_columns = 48;
inline constexpr std::size_t causal_square_degree = 16;
inline constexpr std::size_t causal_polynomial_capacity = 17;
inline constexpr std::size_t causal_kernel_capacity = 32;

struct causal_linear_card final {
  exact::word schema{};
  exact::word occurrence{};
  exact::word lineage{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  std::uint32_t byte_count{};
  std::int8_t eigen_min{};
  std::int8_t eigen_max{};
  std::uint8_t phase_first{};
  std::uint8_t phase_second{};
  bool parsed{};
};

struct causal_linear_foundation final {
  exact::word ecology{};
  exact::word matrix{};
  exact::word chain{};
  exact::word characteristic{};
  exact::word multilinear{};
  exact::word coefficient_field{};
  exact::word theorem{};
  exact::word provenance{};
  causal_linear_card card{};
  cm_problem_card cm{};
  toric_cycle_card toric{};
  algebraic_variation_card variation{};
};

struct causal_linear_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word material{};
};

enum class causal_linear_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  source_refused,
  matrix_refused,
  chain_refused,
  characteristic_refused,
  coefficient_field_refused,
  aggregation_refused,
  continuation_refused,
  render_refused,
  checker_rejected,
  rest_refused
};

struct causal_linear_plan final {
  exact::word passage{};
  exact::word statement{};
  exact::word lineage{};
  std::uint8_t source_mask{};
  bool matrices_exact{};
  bool chains_exact{};
  bool characteristics_exact{};
  bool multilinear_exact{};
  bool controls_exact{};
};

struct acquired_causal_linear final {
  exact::word identity{};
  exact::word passage{};
  exact::word kernel_return{};
  exact::word lineage{};
  exact::word admitted_tally_delta{};
  bool accepted{};
};

}  // namespace holonics::organ
