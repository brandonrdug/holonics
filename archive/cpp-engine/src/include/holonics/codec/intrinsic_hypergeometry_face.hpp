#pragma once

#include <holonics/codec/blind_reconstruction_face.hpp>

namespace holonics::codec {

inline constexpr std::size_t intrinsic_hypergeometry_formal_capacity = 32'768;
inline constexpr std::size_t intrinsic_hypergeometry_explanation_capacity = 4'096;
inline constexpr std::size_t intrinsic_hypergeometry_case_capacity = 10;

using intrinsic_hypergeometry_formal_face =
    blind_formal_face<intrinsic_hypergeometry_formal_capacity>;

struct intrinsic_hypergeometry_explanation final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[intrinsic_hypergeometry_explanation_capacity]{};
};

struct intrinsic_case_surface final {
  std::uint32_t transition_rows[4]{};
  std::uint32_t section_return[4]{};
  std::uint16_t seams[4]{};
  std::uint16_t vertices{};
  std::uint16_t edges{};
  std::uint16_t faces{};
  std::uint16_t flags{};
  std::uint16_t lcm{};
  std::uint8_t tours{};
};

struct intrinsic_hypergeometry_surface final {
  intrinsic_case_surface cases[intrinsic_hypergeometry_case_capacity]{};
  intrinsic_case_surface changed{};
  std::int64_t phase_characteristic[5]{};
  std::int64_t cm_characteristic[5]{};
  std::int64_t commutator[4]{};
  exact::word passage{};
  std::uint8_t square_count{};
  bool incidence_exact{};
  bool distributions_exact{};
  bool sections_exact{};
  bool supports_separated{};
  bool controls_exact{};
  bool changed_sensitive{};
  bool alternatives_retained{};
};

}  // namespace holonics::codec
