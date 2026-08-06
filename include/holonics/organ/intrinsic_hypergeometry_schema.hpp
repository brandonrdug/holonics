#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>
#include <holonics/organ/algebraic_variation_schema.hpp>
#include <holonics/organ/cm_incidence_schema.hpp>

namespace holonics::organ {

inline constexpr std::size_t intrinsic_case_capacity = 10;
inline constexpr std::size_t intrinsic_vertex_capacity = 17U * 19U;
inline constexpr std::size_t intrinsic_edge_capacity = 2U * intrinsic_vertex_capacity;
inline constexpr std::size_t intrinsic_face_capacity = intrinsic_vertex_capacity;
inline constexpr std::size_t intrinsic_flag_capacity = 8U * intrinsic_face_capacity;
inline constexpr std::size_t intrinsic_series_capacity = 20;
inline constexpr std::size_t intrinsic_cm_square_capacity = 40;
inline constexpr std::size_t intrinsic_tour_capacity = 19;

enum class intrinsic_seam : std::uint8_t { interior, first, second, simultaneous };

struct intrinsic_presentation final {
  std::uint16_t first{};
  std::uint16_t second{};
  std::uint8_t rechart{};
};

struct intrinsic_hypergeometry_card final {
  exact::word schema{};
  exact::word occurrence{};
  exact::word lineage{};
  std::uint64_t byte_fold{};
  std::uint64_t path_fold{};
  std::uint32_t byte_count{};
  intrinsic_presentation cases[intrinsic_case_capacity]{};
  std::uint32_t section_modulus{};
  std::uint8_t receiver_first_weight{};
  std::uint8_t receiver_second_weight{};
  std::uint8_t receiver_denominator{};
  std::uint8_t series_depth{};
  std::uint8_t case_count{};
  bool parsed{};
};

struct intrinsic_hypergeometry_foundation final {
  exact::word ecology{};
  exact::word incidence{};
  exact::word chronology{};
  exact::word receiver{};
  exact::word local_system{};
  exact::word characteristic{};
  exact::word theorem{};
  exact::word provenance{};
  intrinsic_hypergeometry_card card{};
  cm_problem_card cm{};
  algebraic_variation_card variation{};
};

struct intrinsic_hypergeometry_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word material{};
};

enum class intrinsic_hypergeometry_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  incidence_refused,
  chronology_refused,
  projection_refused,
  section_refused,
  composition_refused,
  control_refused,
  continuation_refused,
  render_refused,
  checker_rejected,
  rest_refused
};

struct intrinsic_hypergeometry_plan final {
  exact::word passage{};
  exact::word statement{};
  exact::word lineage{};
  std::uint16_t source_mask{};
  bool incidence_exact{};
  bool distributions_exact{};
  bool sections_exact{};
  bool supported_cycles_exact{};
  bool controls_exact{};
};

struct acquired_intrinsic_hypergeometry final {
  exact::word identity{};
  exact::word passage{};
  exact::word kernel_return{};
  exact::word lineage{};
  exact::word admitted_tally_delta{};
  bool accepted{};
};

}  // namespace holonics::organ
