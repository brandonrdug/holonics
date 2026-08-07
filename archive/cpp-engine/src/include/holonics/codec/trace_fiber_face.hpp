#pragma once

#include <holonics/codec/characteristic_hypergeometry_face.hpp>

namespace holonics::codec {

using trace_fiber_formal_face = elementary_formal_face;
using trace_fiber_dossier_face = elementary_dossier_face;
inline constexpr std::uint8_t trace_fiber_surface_features = 85;
inline constexpr std::uint8_t trace_fiber_surface_witnesses = 5;
struct trace_fiber_triple_surface final {
  elementary_matrix2_surface matrices[8]{};
  std::int64_t lower[6]{};
  std::int64_t ordered[2]{};
  std::uint16_t words[3]{};
  std::uint8_t source{};
};
struct trace_fiber_discovery_surface final {
  std::int64_t coefficients[2][trace_fiber_surface_features]{};
  trace_fiber_triple_surface witnesses[trace_fiber_surface_witnesses][2]{};
  std::uint16_t triple_count[3]{};
  std::uint16_t group_count{};
  std::uint16_t branch_count{};
  std::uint16_t two_sheet_count{};
  exact::word passage{};
  bool exact{};
};
struct heldout_trace_fiber_surface final {
  elementary_matrix2_surface matrices[8]{};
  std::int64_t lower[6]{};
  std::int64_t anchor{};
  std::int64_t companion{};
  std::int64_t source_companion{};
  std::int64_t symmetric[2]{};
  std::int64_t quadratic[3]{};
  std::int64_t roots[2]{};
  std::int64_t discriminant{};
  exact::word passage{};
  bool prediction_before_comparison{};
  bool source_detached{};
  bool exact{};
};

} // namespace holonics::codec
