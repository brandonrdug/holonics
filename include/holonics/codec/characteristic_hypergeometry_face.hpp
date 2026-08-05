#pragma once

#include <holonics/codec/elementary_calculus_face.hpp>

namespace holonics::codec {

using characteristic_formal_face = elementary_formal_face;
using characteristic_dossier_face = elementary_dossier_face;
inline constexpr std::uint8_t characteristic_surface_source_count = 3;
inline constexpr std::uint8_t characteristic_surface_feature_count = 21;
inline constexpr std::uint8_t characteristic_surface_witness_count = 5;
struct characteristic_pair_surface final {
  elementary_matrix2_surface first{};
  elementary_matrix2_surface second{};
  elementary_matrix2_surface product{};
  elementary_matrix2_surface closed{};
  std::int64_t trace_first{};
  std::int64_t trace_second{};
  std::int64_t trace_product{};
  std::int64_t trace_closed{};
  std::uint16_t left_word{};
  std::uint16_t right_word{};
  std::uint8_t source{};
};

struct characteristic_hypergeometry_surface final {
  std::int64_t coefficients[characteristic_surface_feature_count]{};
  characteristic_pair_surface witnesses[characteristic_surface_witness_count]
                                       [2]{};
  std::uint16_t pair_count[characteristic_surface_source_count]{};
  std::uint16_t group_count{};
  std::uint16_t closed_strata[3]{};
  exact::word passage{};
  bool exact{};
};

struct heldout_characteristic_surface final {
  std::int64_t visible[3]{};
  std::int64_t predicted_trace{};
  std::int64_t source_trace{};
  std::int64_t predicted_discriminant{};
  std::int64_t characteristic[3]{};
  std::uint8_t fixed_rank{};
  exact::word passage{};
  bool prediction_before_comparison{};
  bool source_detached{};
  bool exact{};
};

} // namespace holonics::codec
