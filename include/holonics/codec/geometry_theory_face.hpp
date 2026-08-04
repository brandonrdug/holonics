#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::codec {

inline constexpr std::size_t geometry_theory_source_capacity = 8192;
inline constexpr std::size_t geometry_theory_explanation_capacity = 2048;

struct geometry_theory_surface final {
  exact::word passage{};
  exact::word auxiliary_statement{};
  exact::word affine_statement{};
  exact::word fractional_statement{};
  exact::word counterexample_statement{};
  bool difference_factor{};
  bool affine_common_square{};
  bool fractional_invariance{};
  bool coordinate_counterexample{};
  bool singular_boundary{};
};

struct geometry_theory_face final {
  exact::word identity{};
  exact::word passage{};
  std::uint32_t byte_count{};
  char bytes[geometry_theory_source_capacity]{};
};

struct geometry_theory_explanation final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[geometry_theory_explanation_capacity]{};
};

template<std::size_t Capacity, class Count, std::size_t Source>
HOLONICS_CALLABLE constexpr bool append_geometry_face(
    char (&destination)[Capacity], Count& used, const char (&source)[Source]) noexcept {
  constexpr std::size_t payload = Source - 1U;
  if (static_cast<std::size_t>(used) + payload > Capacity) { return false; }
  for (std::size_t slot = 0; slot < payload; ++slot) {
    destination[used++] = source[slot];
  }
  return true;
}

}  // namespace holonics::codec
