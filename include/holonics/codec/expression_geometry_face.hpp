#pragma once

#include <holonics/codec/blind_reconstruction_face.hpp>
#include <holonics/exact/small_rational.hpp>

namespace holonics::codec {

inline constexpr std::size_t expression_geometry_formal_capacity = 65'536;
inline constexpr std::size_t expression_geometry_explanation_capacity = 4'096;
using expression_geometry_formal_face = blind_formal_face<expression_geometry_formal_capacity>;

struct expression_geometry_explanation final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[expression_geometry_explanation_capacity]{};
};

struct expression_geometry_surface final {
  std::int64_t resultant[6]{};
  std::int64_t changed_resultant[6]{};
  std::int64_t bezout_f[4][21]{};
  std::int64_t bezout_fx[5][21]{};
  std::int64_t reduction_p[4][4][21]{};
  std::int64_t reduction_q[4][5][21]{};
  std::int64_t scalar[6]{};
  std::int64_t finite_indicial[5]{};
  std::int64_t infinity_indicial[5]{};
  exact::small_rational series[4][11]{};
  exact::small_rational changed_series{};
  exact::small_rational residue_entry[5]{};
  exact::small_rational residue[4][4][5]{};
  std::int64_t translated_constant[6]{};
  std::int64_t translated_parameter[6]{};
  exact::word passage{};
  exact::word fiber_members[3]{};
  std::int8_t rational_shift{};
  std::int8_t gaussian_x_scale{};
  std::int8_t gaussian_y_square{};
  std::uint8_t singular_count{};
  std::int64_t family_constant{};
  bool ideals_exact{};
  bool differential_exact{};
  bool residue_exact{};
  bool fibers_exact{};
  bool changed_sensitive{};
  bool alternatives_retained{};
};

}  // namespace holonics::codec
