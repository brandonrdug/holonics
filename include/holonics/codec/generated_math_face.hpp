#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/word.hpp>

namespace holonics::codec {

inline constexpr std::size_t formal_math_face_capacity = 1024;
inline constexpr std::size_t conversational_math_face_capacity = 512;

struct generated_math_surface final {
  exact::word passage{};
  exact::word statement{};
  exact::word proof{};
  exact::word premise_declaration{};
  std::uint8_t statement_form{};
  std::uint8_t proof_form{};
};

struct formal_math_face final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[formal_math_face_capacity]{};
};

struct conversational_math_face final {
  exact::word identity{};
  exact::word passage{};
  std::uint16_t byte_count{};
  char bytes[conversational_math_face_capacity]{};
};

template<std::size_t Capacity, std::size_t Count>
HOLONICS_CALLABLE constexpr bool append_face(
    char (&destination)[Capacity], std::uint16_t& used, const char (&source)[Count]) noexcept {
  constexpr std::size_t payload = Count - 1U;
  if (static_cast<std::size_t>(used) + payload > Capacity) { return false; }
  for (std::size_t slot = 0; slot < payload; ++slot) {
    destination[used++] = source[slot];
  }
  return true;
}

}  // namespace holonics::codec
