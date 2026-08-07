#pragma once

#include <cstdint>

#include <holonics/codec/blind_reconstruction_face.hpp>

namespace holonics::codec {

inline constexpr std::size_t arithmetic_formal_capacity = 32'768;
inline constexpr std::size_t arithmetic_explanation_capacity = 4'096;
inline constexpr std::size_t arithmetic_surface_degree_count = 4;
inline constexpr std::size_t arithmetic_surface_curve_count = 7;
using arithmetic_formal_face = blind_formal_face<arithmetic_formal_capacity>;

struct arithmetic_explanation final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[arithmetic_explanation_capacity]{};
};

struct arithmetic_curve_surface final {
  std::int64_t prime{};
  std::int64_t coefficient{};
  std::int64_t a{};
  std::int64_t b{};
  std::int64_t counts[arithmetic_surface_degree_count]{};
  std::int64_t traces[arithmetic_surface_degree_count + 1]{};
  std::int64_t places[arithmetic_surface_degree_count]{};
  std::int64_t homogeneous[arithmetic_surface_degree_count + 1][2]{};
};

struct arithmetic_spectral_surface final {
  arithmetic_curve_surface curves[arithmetic_surface_curve_count]{};
  exact::word passage{};
  std::uint32_t fixed_contributions{};
  std::uint32_t candidate_count{};
  std::uint32_t point_count{};
  std::uint32_t trace_current_count{};
  std::uint32_t norm_current_count{};
  std::uint16_t rechart_scale{};
  bool fields_exact{};
  bool correspondences_exact{};
  bool forms_exact{};
  bool traces_exact{};
  bool controls_exact{};
  bool archimedean_inapplicable{};
  bool alternatives_retained{};
};

}  // namespace holonics::codec
