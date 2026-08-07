#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::codec {

inline constexpr std::size_t blind_code_source_capacity = 24'576;
inline constexpr std::size_t blind_moment_source_capacity = 12'288;
inline constexpr std::size_t blind_explanation_capacity = 4'096;
inline constexpr std::size_t blind_code_cell_capacity = 20;
inline constexpr std::size_t blind_code_degree_capacity = 8;
inline constexpr std::size_t blind_moment_degree_capacity = 4;
inline constexpr std::size_t blind_polynomial_capacity = 5;

struct blind_reconstruction_surface final {
  exact::word passage{};
  exact::word input_lineage{};
  bool incidence{};
  bool characteristic{};
  bool obstruction{};
  bool alternatives{};
  bool source_separated{};
};

struct blind_code_surface final {
  exact::word passage{};
  std::int16_t quotient[blind_code_cell_capacity][blind_code_cell_capacity]{};
  std::int64_t witness[blind_code_cell_capacity]{};
  std::int64_t mass[blind_code_cell_capacity]{};
  std::int64_t weight[blind_code_degree_capacity]{};
  std::int64_t dual[blind_code_degree_capacity]{};
  std::int64_t krawtchouk[blind_code_degree_capacity][blind_code_degree_capacity]{};
  std::int64_t multiplicity[blind_code_degree_capacity]{};
  std::int16_t eigenvalue{};
  std::uint8_t cell_count{};
  bool incidence{};
  bool characteristic{};
  bool alternatives{};
  bool source_separated{};
};

struct blind_moment_surface final {
  exact::word passage{};
  std::int64_t hankel[blind_moment_degree_capacity][blind_moment_degree_capacity]{};
  std::int64_t shifted[blind_moment_degree_capacity][blind_moment_degree_capacity]{};
  std::int64_t collision[blind_moment_degree_capacity][blind_moment_degree_capacity]{};
  std::int64_t polynomial[blind_polynomial_capacity]{};
  std::int64_t roots[blind_moment_degree_capacity]{};
  std::int64_t determinant{};
  std::int64_t discriminant{};
  std::uint8_t degree{};
  std::uint8_t root_count{};
  bool incidence{};
  bool characteristic{};
  bool obstruction{};
  bool alternatives{};
  bool source_separated{};
};

template<std::size_t Capacity>
struct blind_formal_face final {
  exact::word identity{};
  exact::word passage{};
  std::uint32_t byte_count{};
  char bytes[Capacity]{};
};

struct blind_explanation final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[blind_explanation_capacity]{};
};

using blind_code_face = blind_formal_face<blind_code_source_capacity>;
using blind_moment_face = blind_formal_face<blind_moment_source_capacity>;

template<std::size_t Capacity, class Count, std::size_t Source>
HOLONICS_CALLABLE constexpr bool append_blind(
    char (&destination)[Capacity], Count& used, const char (&source)[Source]) noexcept {
  constexpr std::size_t payload = Source - 1U;
  if (static_cast<std::size_t>(used) + payload > Capacity) { return false; }
  for (std::size_t slot = 0; slot < payload; ++slot) { destination[used++] = source[slot]; }
  return true;
}

template<std::size_t Capacity, class Count>
HOLONICS_CALLABLE constexpr bool append_blind_char(
    char (&destination)[Capacity], Count& used, char value) noexcept {
  if (static_cast<std::size_t>(used) >= Capacity) { return false; }
  destination[used++] = value;
  return true;
}

template<std::size_t Capacity, class Count>
HOLONICS_CALLABLE constexpr bool append_blind_integer(
    char (&destination)[Capacity], Count& used, std::int64_t value) noexcept {
  if (value < 0 && !append_blind_char(destination, used, '-')) { return false; }
  std::uint64_t magnitude = value < 0 ?
      static_cast<std::uint64_t>(-(value + 1)) + 1U : static_cast<std::uint64_t>(value);
  char digits[20]{};
  std::uint8_t count = 0;
  do {
    digits[count++] = static_cast<char>('0' + magnitude % 10U);
    magnitude /= 10U;
  } while (magnitude != 0);
  while (count > 0) {
    if (!append_blind_char(destination, used, digits[--count])) { return false; }
  }
  return true;
}

}  // namespace holonics::codec
