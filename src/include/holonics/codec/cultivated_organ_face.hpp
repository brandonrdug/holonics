#pragma once

#include <holonics/codec/blind_reconstruction_face.hpp>
#include <holonics/exact/small_rational.hpp>

namespace holonics::codec {

inline constexpr std::size_t cultivated_formal_capacity = 32'768;
inline constexpr std::size_t cultivated_dossier_capacity = 12'288;
using cultivated_formal_face = blind_formal_face<cultivated_formal_capacity>;

struct cultivated_dossier_face final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[cultivated_dossier_capacity]{};
};

inline constexpr std::uint8_t cultivated_surface_family_count = 4;
inline constexpr std::uint8_t cultivated_surface_series_count = 4;
inline constexpr std::uint8_t cultivated_surface_sample_count = 10;
inline constexpr std::uint8_t cultivated_surface_feature_count = 12;

struct cultivated_kernel_surface final {
  exact::small_rational samples[cultivated_surface_series_count]
                               [cultivated_surface_sample_count]{};
  std::int64_t coefficients[cultivated_surface_feature_count]{};
  std::uint8_t sample_count[cultivated_surface_series_count]{};
  std::uint8_t series_count{};
  std::uint8_t order{};
  std::uint8_t degree{};
  std::uint8_t features{};
};

struct cultivation_surface final {
  cultivated_kernel_surface kernels[cultivated_surface_family_count]{};
  exact::word passage{};
  bool exact{};
};

struct cultivated_tail_surface final {
  exact::small_rational source[cultivated_surface_sample_count]{};
  exact::small_rational predicted[cultivated_surface_sample_count]{};
  std::uint8_t sample_count{};
  std::uint8_t prefix_count{};
  std::uint8_t changed_source{};
  std::uint8_t short_prefix{};
  std::uint8_t exclusion{};
  bool exact{};
};

struct cultivated_application_surface final {
  cultivated_kernel_surface kernels[cultivated_surface_family_count]{};
  cultivated_tail_surface tails[cultivated_surface_family_count]{};
  exact::word passage{};
  bool source_detached{};
  bool exact{};
};

}  // namespace holonics::codec
