#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::codec {

inline constexpr std::size_t regular_singular_source_capacity = 12'288;
inline constexpr std::size_t regular_singular_explanation_capacity = 4'096;

struct regular_singular_surface final {
  exact::word passage{};
  bool residue_algebra{};
  bool frobenius_steps{};
  bool resonance_obstruction{};
  bool chamber_connection{};
  bool loop_product{};
  bool lineage_retained{};
};

struct regular_singular_face final {
  exact::word identity{};
  exact::word passage{};
  std::uint32_t byte_count{};
  char bytes[regular_singular_source_capacity]{};
};

struct regular_singular_explanation final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[regular_singular_explanation_capacity]{};
};

template<std::size_t Capacity, class Count, std::size_t Source>
HOLONICS_CALLABLE constexpr bool append_regular_singular(
    char (&destination)[Capacity], Count& used, const char (&source)[Source]) noexcept {
  constexpr std::size_t payload = Source - 1U;
  if (static_cast<std::size_t>(used) + payload > Capacity) { return false; }
  for (std::size_t slot = 0; slot < payload; ++slot) { destination[used++] = source[slot]; }
  return true;
}

}  // namespace holonics::codec
