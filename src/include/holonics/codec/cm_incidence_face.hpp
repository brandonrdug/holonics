#pragma once

#include <holonics/codec/blind_reconstruction_face.hpp>

namespace holonics::codec {

inline constexpr std::size_t cm_formal_capacity = 24'576;
inline constexpr std::size_t cm_explanation_capacity = 4'096;
inline constexpr std::size_t cm_degree_capacity = 4;
inline constexpr std::size_t cm_translation_capacity = 5;
inline constexpr std::size_t cm_characteristic_capacity = 17;
inline constexpr std::size_t cm_factor_capacity = 6;

using cm_formal_face = blind_formal_face<cm_formal_capacity>;

struct cm_element_surface final {
  std::int64_t coefficients[cm_degree_capacity]{};
};

struct cm_factor_surface final {
  std::int64_t coefficients[cm_factor_capacity]{};
  std::uint8_t degree{};
  std::uint8_t multiplicity{};
  bool exact{};
};

struct cm_explanation final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[cm_explanation_capacity]{};
};

struct cm_incidence_surface final {
  exact::word passage{};
  cm_element_surface translations[cm_translation_capacity]{};
  cm_factor_surface periodic_factors[cm_factor_capacity]{};
  cm_factor_surface window_factors[cm_factor_capacity]{};
  std::int64_t periodic_characteristic[cm_characteristic_capacity]{};
  std::int64_t window_characteristic[cm_characteristic_capacity]{};
  std::uint8_t direction_population[cm_translation_capacity]{};
  std::uint8_t periodic_factor_count{};
  std::uint8_t window_factor_count{};
  std::uint8_t periodic_edges{};
  std::uint8_t window_edges{};
  std::uint8_t lost_edges{};
  std::uint8_t unit_pairs{};
  std::uint8_t projection_loss{};
  bool norm_one{};
  bool incidence_agreement{};
  bool characteristic_transport{};
  bool aperture_scattering{};
  bool alternatives_retained{};
};

}  // namespace holonics::codec
