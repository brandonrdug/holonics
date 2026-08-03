#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/integer.hpp>

namespace holonics::exact {

template<std::size_t Capacity>
struct big_endian_bytes final {
  std::uint8_t octets[Capacity * 8]{};
};

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr big_endian_bytes<Capacity> encode_big_endian(
    const unsigned_integer<Capacity>& value) noexcept {
  big_endian_bytes<Capacity> result{};
  for (std::size_t limb_index = 0; limb_index < Capacity; ++limb_index) {
    std::uint64_t limb = value.limb(limb_index);
    for (std::size_t octet = 0; octet < 8; ++octet) {
      const std::size_t destination = Capacity * 8 - 1 - (limb_index * 8 + octet);
      result.octets[destination] = static_cast<std::uint8_t>(limb & 255U);
      limb >>= 8U;
    }
  }
  return result;
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr unsigned_integer<Capacity> decode_big_endian(
    const big_endian_bytes<Capacity>& bytes) noexcept {
  unsigned_integer<Capacity> result{};
  for (std::size_t limb_index = 0; limb_index < Capacity; ++limb_index) {
    std::uint64_t limb = 0;
    for (std::size_t octet = 0; octet < 8; ++octet) {
      const std::size_t source = Capacity * 8 - 1 - (limb_index * 8 + octet);
      limb |= static_cast<std::uint64_t>(bytes.octets[source]) << (octet * 8);
    }
    result.set_limb(limb_index, limb);
  }
  result.normalize();
  return result;
}

}  // namespace holonics::exact
