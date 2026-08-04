#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::codec {

inline constexpr std::size_t phase_crystal_source_capacity = 8192;
inline constexpr std::size_t phase_crystal_explanation_capacity = 2048;

struct phase_crystal_surface final {
  exact::word passage{};
  exact::word diagonal_statement{};
  exact::word coprime_statement{};
  exact::word population_statement{};
  exact::word series_statement{};
  bool diagonal_lcm{};
  bool coprime_full_tour{};
  bool cell_population_product{};
  bool seam_cancellation{};
  bool gauss_transport{};
  bool projection_distinguished{};
};

struct phase_crystal_face final {
  exact::word identity{};
  exact::word passage{};
  std::uint32_t byte_count{};
  char bytes[phase_crystal_source_capacity]{};
};

struct phase_crystal_explanation final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[phase_crystal_explanation_capacity]{};
};

template<std::size_t Capacity, class Count, std::size_t Source>
HOLONICS_CALLABLE constexpr bool append_phase_crystal(
    char (&destination)[Capacity], Count& used, const char (&source)[Source]) noexcept {
  constexpr std::size_t payload = Source - 1U;
  if (static_cast<std::size_t>(used) + payload > Capacity) { return false; }
  for (std::size_t slot = 0; slot < payload; ++slot) { destination[used++] = source[slot]; }
  return true;
}

}  // namespace holonics::codec
