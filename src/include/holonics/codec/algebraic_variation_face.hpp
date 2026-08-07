#pragma once

#include <holonics/codec/blind_reconstruction_face.hpp>
#include <holonics/exact/small_rational.hpp>

namespace holonics::codec {

inline constexpr std::size_t variation_formal_capacity = 12'288;
inline constexpr std::size_t variation_explanation_capacity = 4'096;

using variation_formal_face = blind_formal_face<variation_formal_capacity>;

struct variation_explanation final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[variation_explanation_capacity]{};
};

struct algebraic_variation_surface final {
  exact::word passage{};
  std::int64_t polynomial[4][2]{};
  std::int64_t discriminant[5]{};
  std::int64_t roots[3][2]{};
  std::int64_t collision_parameters[2]{};
  std::uint8_t collision_multiplicities[2]{};
  std::int64_t connection_numerator[2][2][2]{};
  std::int64_t connection_pole[3]{};
  std::int64_t connection_scale{};
  std::int64_t witness[2][3][2]{};
  std::int64_t invariant[2][2]{};
  std::int64_t scalar_second[3]{};
  std::int64_t scalar_first[2]{};
  std::int64_t scalar_zeroth{};
  exact::small_rational series[8]{};
  std::int64_t monodromy[3][2][2]{};
  std::uint8_t series_count{};
  std::uint8_t root_count{};
  std::uint8_t collision_count{};
  std::uint8_t invariant_survivors{};
  std::uint8_t retained_candidates{};
  bool family_exact{};
  bool reduction_exact{};
  bool connection_exact{};
  bool invariant_exact{};
  bool operator_exact{};
  bool loops_exact{};
  bool selection_exact{};
  bool alternatives_retained{};
};

}  // namespace holonics::codec
