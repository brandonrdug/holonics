#pragma once

#include <holonics/codec/blind_reconstruction_face.hpp>

namespace holonics::codec {

inline constexpr std::size_t toric_formal_capacity = 12'288;
inline constexpr std::size_t toric_explanation_capacity = 4'096;

using toric_formal_face = blind_formal_face<toric_formal_capacity>;

struct toric_explanation final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[toric_explanation_capacity]{};
};

struct toric_cycle_surface final {
  exact::word passage{};
  std::int64_t rays[3][5][2]{};
  std::int64_t cone_determinants[3][5]{};
  std::int64_t divisor_classes[2][5][3]{};
  std::int64_t principal_relations[2][2][5]{};
  std::int64_t base_form[2][2]{};
  std::int64_t integral_class[2]{};
  std::int64_t integral_response[2]{};
  std::int64_t rational_numerator{};
  std::int64_t rational_denominator{};
  std::int64_t incompatible_response[4]{};
  std::int64_t negative_class[2]{};
  std::int64_t negative_square{};
  std::int64_t blowup_form[2][2]{};
  std::int64_t exceptional[2]{};
  std::int64_t exceptional_square{};
  std::int64_t blowup_negative[2]{};
  std::int64_t blowup_negative_square{};
  std::int64_t derived_ray[2]{};
  std::int64_t strict_transforms[3][2]{};
  std::int64_t total_transforms[3][2]{};
  std::int64_t pullback[2]{};
  std::int64_t pushforward[2]{};
  std::uint8_t ray_counts[3]{};
  std::uint8_t quotient_ranks[3]{};
  std::uint8_t middle_betti[3]{};
  std::uint8_t middle_hodge[3]{};
  bool fan_chow_agree{};
  bool inverse_fibers_exact{};
  bool blowup_transport_exact{};
  bool alternatives_retained{};
};

}  // namespace holonics::codec
