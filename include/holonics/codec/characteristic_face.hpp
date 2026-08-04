#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::codec {

inline constexpr std::size_t characteristic_source_capacity = 10'240;
inline constexpr std::size_t characteristic_explanation_capacity = 3'072;

struct characteristic_surface final {
  exact::word passage{};
  bool diagonal_factor{};
  bool weighted_cycle{};
  bool matrix_controls{};
  bool discriminants_typed{};
  bool gauss_indicial{};
  bool lineage_retained{};
};

struct characteristic_face final {
  exact::word identity{};
  exact::word passage{};
  std::uint32_t byte_count{};
  char bytes[characteristic_source_capacity]{};
};

struct characteristic_explanation final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[characteristic_explanation_capacity]{};
};

template<std::size_t Capacity, class Count, std::size_t Source>
HOLONICS_CALLABLE constexpr bool append_characteristic(
    char (&destination)[Capacity], Count& used, const char (&source)[Source]) noexcept {
  constexpr std::size_t payload = Source - 1U;
  if (static_cast<std::size_t>(used) + payload > Capacity) { return false; }
  for (std::size_t slot = 0; slot < payload; ++slot) { destination[used++] = source[slot]; }
  return true;
}

}  // namespace holonics::codec
