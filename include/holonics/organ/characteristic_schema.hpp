#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>
#include <holonics/organ/phase_crystal_schema.hpp>

namespace holonics::organ {

inline constexpr std::size_t characteristic_case_capacity = phase_crystal_case_capacity;
inline constexpr std::size_t characteristic_shape_capacity = phase_crystal_point_capacity;
inline constexpr std::size_t characteristic_tour_capacity = 4;

enum class characteristic_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  orbit_refused,
  shape_transport_refused,
  scalar_control_refused,
  matrix_control_refused,
  indicial_refused,
  continuation_refused,
  render_refused,
  checker_rejected,
  rest_refused
};

struct matrix_two final {
  std::int64_t a{};
  std::int64_t b{};
  std::int64_t c{};
  std::int64_t d{};
};

struct characteristic_foundation final {
  exact::word ecology{};
  exact::word cyclic_transport{};
  exact::word shape_transport{};
  exact::word matrix_transport{};
  exact::word discriminant{};
  exact::word indicial{};
  exact::word provenance{};
  exact::word case_seed{};
  std::uint16_t case_count{};
};

struct characteristic_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word material{};
};

struct characteristic_theory_plan final {
  exact::word passage{};
  exact::word diagonal_statement{};
  exact::word weighted_statement{};
  exact::word matrix_statement{};
  exact::word indicial_statement{};
  exact::word lineage{};
  bool diagonal_factor{};
  bool weighted_cycle{};
  bool matrix_controls{};
  bool discriminants_typed{};
  bool gauss_indicial{};
  bool lineage_retained{};
};

struct acquired_characteristic final {
  exact::word identity{};
  exact::word passage{};
  exact::word kernel_return{};
  exact::word lineage{};
  exact::word morphology_delta{};
  bool accepted{};
};

}  // namespace holonics::organ
