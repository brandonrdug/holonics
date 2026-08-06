#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::organ {

inline constexpr std::size_t cm_degree_capacity = 4;
inline constexpr std::size_t cm_translation_capacity = 5;
inline constexpr std::size_t cm_point_capacity = 16;
inline constexpr std::size_t cm_edge_capacity = 40;
inline constexpr std::size_t cm_characteristic_capacity = 17;
inline constexpr std::size_t cm_factor_capacity = 6;
inline constexpr std::size_t cm_candidate_capacity = 3;

enum class cm_candidate_kind : std::uint8_t {
  four_direction_collapse,
  modular_wrap_window,
  coefficient_sum_projection
};

enum class cm_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  arithmetic_refused,
  incidence_refused,
  characteristic_refused,
  factor_refused,
  continuation_refused,
  render_refused,
  checker_rejected,
  rest_refused
};

struct cm_element final {
  std::int64_t coefficients[cm_degree_capacity]{};
};

struct cm_problem_card final {
  exact::word schema{};
  exact::word occurrence{};
  exact::word lineage{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  std::uint32_t byte_count{};
  std::int16_t factor_min{};
  std::int16_t factor_max{};
  std::uint8_t cyclotomic_order{};
  std::uint8_t degree{};
  std::uint8_t periodic_modulus{};
  std::int8_t window_min{};
  std::int8_t window_max{};
  std::uint8_t translation_count{};
  bool parsed{};
};

struct cm_incidence_foundation final {
  exact::word ecology{};
  exact::word arithmetic{};
  exact::word translation{};
  exact::word incidence{};
  exact::word characteristic{};
  exact::word projection{};
  exact::word provenance{};
  cm_problem_card card{};
};

struct cm_incidence_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word material{};
};

struct cm_theory_plan final {
  exact::word passage{};
  exact::word statement{};
  exact::word lineage{};
  bool norm_one{};
  bool incidence_agreement{};
  bool characteristic_transport{};
  bool aperture_scattering{};
  bool alternatives_retained{};
};

struct acquired_cm_incidence final {
  exact::word identity{};
  exact::word passage{};
  exact::word kernel_return{};
  exact::word lineage{};
  exact::word admitted_tally_delta{};
  bool accepted{};
};

}  // namespace holonics::organ
