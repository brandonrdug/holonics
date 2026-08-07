#pragma once

#include <cstdint>

#include <holonics/exact/integer_division.hpp>

namespace holonics::codec::rederivation_render_detail {

template <class Face> struct writer final {
  Face &face;
  HOLONICS_CALLABLE bool character(char value) noexcept {
    if (face.byte_count >= sizeof(face.bytes))
      return false;
    face.bytes[face.byte_count++] = value;
    return true;
  }
  HOLONICS_CALLABLE bool text(const char *value) noexcept {
    for (std::size_t i = 0; value[i] != '\0'; ++i)
      if (!character(value[i]))
        return false;
    return true;
  }
  HOLONICS_CALLABLE bool natural(std::uint64_t value) noexcept {
    char digits[24]{};
    std::uint8_t used = 0;
    do {
      const auto division = exact::divide_unsigned(value, 10U);
      digits[used++] = static_cast<char>('0' + division.remainder);
      value = division.quotient;
    } while (value != 0);
    while (used != 0)
      if (!character(digits[--used]))
        return false;
    return true;
  }
  HOLONICS_CALLABLE bool integer(std::int64_t value) noexcept {
    if (value < 0) {
      if (!text("("))
        return false;
      if (!character('-'))
        return false;
      const auto magnitude = static_cast<std::uint64_t>(-(value + 1)) + 1U;
      return natural(magnitude) && text(")");
    }
    return natural(static_cast<std::uint64_t>(value));
  }
};

} // namespace holonics::codec::rederivation_render_detail
