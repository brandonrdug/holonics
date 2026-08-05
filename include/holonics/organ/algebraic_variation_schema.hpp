#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/small_rational.hpp>
#include <holonics/exact/word.hpp>

namespace holonics::organ {

inline constexpr std::size_t variation_coefficient_count = 4;
inline constexpr std::size_t variation_sample_capacity = 9;
inline constexpr std::size_t variation_polynomial_capacity = 9;
inline constexpr std::size_t variation_root_capacity = 6;
inline constexpr std::size_t variation_collision_capacity = 6;
inline constexpr std::size_t variation_series_capacity = 8;
inline constexpr std::size_t variation_candidate_capacity = 8;

struct affine_integer_coefficient final {
  std::int64_t constant{};
  std::int64_t parameter{};
};

struct algebraic_variation_card final {
  exact::word schema{};
  exact::word occurrence{};
  exact::word lineage{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  std::uint32_t byte_count{};
  affine_integer_coefficient coefficients[variation_coefficient_count]{};
  exact::small_rational samples[variation_sample_capacity]{};
  std::int8_t root_min{};
  std::int8_t root_max{};
  std::int8_t form_min{};
  std::int8_t form_max{};
  std::uint8_t degree{};
  std::uint8_t cover_degree{};
  std::uint8_t sample_count{};
  std::uint8_t discovery_count{};
  std::uint8_t series_depth{};
  bool parsed{};
};

struct algebraic_variation_foundation final {
  exact::word ecology{};
  exact::word family{};
  exact::word differential{};
  exact::word connection{};
  exact::word invariant{};
  exact::word loop{};
  exact::word theorem{};
  exact::word provenance{};
  algebraic_variation_card card{};
};

struct algebraic_variation_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word material{};
};

enum class variation_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  polynomial_refused,
  root_section_refused,
  singular_fiber,
  reduction_refused,
  connection_refused,
  invariant_refused,
  operator_refused,
  loop_refused,
  theorem_section_open,
  continuation_refused,
  render_refused,
  checker_rejected,
  rest_refused
};

struct algebraic_variation_plan final {
  exact::word passage{};
  exact::word statement{};
  exact::word lineage{};
  bool polynomial_exact{};
  bool connection_exact{};
  bool invariant_exact{};
  bool operator_exact{};
  bool loop_exact{};
  bool selected_from_returns{};
};

struct acquired_algebraic_variation final {
  exact::word identity{};
  exact::word passage{};
  exact::word kernel_return{};
  exact::word lineage{};
  exact::word morphology_delta{};
  bool accepted{};
};

}  // namespace holonics::organ
