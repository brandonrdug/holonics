#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::organ {

inline constexpr std::size_t geometry_inquiry_probe_capacity = 32;
inline constexpr std::size_t geometry_inquiry_fiber_capacity = 4;

enum class geometry_conjecture : std::uint8_t {
  raw_coordinate_invariance,
  affine_common_square,
  fractional_cross_ratio,
  singular_quotient_extension
};

enum class geometry_fiber_state : std::uint8_t { open, closed, obstructed };

enum class geometry_inquiry_obstruction : std::uint8_t {
  none,
  invalid_foundation,
  arithmetic_refused,
  coordinate_counterexample,
  singular_chart,
  symbolic_factor_absent,
  continuation_refused,
  render_refused,
  pending_return,
  checker_rejected,
  rest_refused
};

struct inquiry_ratio_pair final {
  exact::word first{};
  exact::word second{};
};

struct geometry_inquiry_foundation final {
  exact::word ecology{};
  exact::word swing_construction{};
  exact::word fractional_chart{};
  exact::word commutative_ring_operations{};
  exact::word field_quotient{};
  exact::word provenance{};
  exact::word probe_seed{};
  std::uint16_t probe_count{};
};

struct geometry_inquiry_question final {
  exact::word identity{};
  exact::word receiver{};
  exact::word material{};
};

struct geometry_conjecture_fiber final {
  exact::word identity{};
  exact::word lineage{};
  geometry_conjecture conjecture{geometry_conjecture::raw_coordinate_invariance};
  geometry_fiber_state state{geometry_fiber_state::open};
  geometry_inquiry_obstruction obstruction{geometry_inquiry_obstruction::none};
  std::uint16_t supporting_probes{};
};

struct geometry_theory_plan final {
  exact::word passage{};
  exact::word auxiliary_statement{};
  exact::word affine_statement{};
  exact::word fractional_statement{};
  exact::word counterexample_statement{};
  exact::word lineage{};
  bool difference_factor{};
  bool affine_common_square{};
  bool fractional_invariance{};
  bool coordinate_counterexample{};
  bool singular_boundary{};
};

struct acquired_geometry_theory final {
  exact::word identity{};
  exact::word passage{};
  exact::word kernel_return{};
  exact::word lineage{};
  exact::word admitted_tally_delta{};
  bool accepted{};
};

}  // namespace holonics::organ
