#pragma once

#include <holonics/exact/rational.hpp>
#include <holonics/organ/causal_linear_receipt.hpp>
#include <holonics/organ/intrinsic_hypergeometry_schema.hpp>

namespace holonics::organ {

struct intrinsic_series_receipt final {
  exact::rational<2> coefficients[intrinsic_series_capacity]{};
  std::int64_t second[3]{};
  std::int64_t first[2]{};
  std::int64_t zeroth{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t count{};
  bool recurrence_exact{};
};

struct intrinsic_local_system_receipt final {
  std::int64_t positive[2][2][2]{};
  std::int64_t inverse[2][2][2]{};
  std::int64_t form[2][2]{};
  std::int64_t ordered_first[2][2]{};
  std::int64_t ordered_second[2][2]{};
  std::int64_t commutator[2][2]{};
  exact::word identity{};
  exact::word lineage{};
  bool form_preserved{};
  bool alternatives_unequal{};
  bool commutator_nontrivial{};
  bool exact{};
};

struct intrinsic_cm_square_receipt final {
  std::uint8_t vertices[4]{};
  std::uint8_t edges[4]{};
  std::uint8_t directions[2]{};
  std::int8_t orientations[4]{};
  std::uint64_t lineage{};
  bool induced{};
  bool boundary_closes{};
  bool filled{};
};

struct intrinsic_supported_cycle_receipt final {
  intrinsic_cm_square_receipt squares[intrinsic_cm_square_capacity]{};
  causal_characteristic_receipt phase_characteristic{};
  causal_characteristic_receipt cm_characteristic{};
  exact::word identity{};
  exact::word lineage{};
  std::uint8_t cm_edge_square_population[40]{};
  std::uint8_t square_count{};
  bool cm_source_exact{};
  bool square_population_exact{};
  bool common_cycle_characteristic{};
  bool phase_cycle_is_boundary{};
  bool cm_cycle_has_no_two_cell{};
  bool oriented_cycle_port_compatible{};
  bool filled_extension_obstructed{};
  bool supported_loop_admitted{};
  bool exact{};
};

struct intrinsic_control_receipt final {
  std::uint32_t rebase_left[4]{};
  std::uint32_t rebase_right[4]{};
  bool equal_hull_unequal_transport{};
  bool equal_local_population_unequal_order{};
  bool equal_spectrum_unequal_support{};
  bool conjugate_rechart{};
  bool changed_source_sensitive{};
  bool exact{};
};

}  // namespace holonics::organ
