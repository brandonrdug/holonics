#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/body/returned_standing.hpp>

namespace holonics::body {

inline constexpr std::uint64_t standing_rest_schema = 0x484F'4C53'5444'0001ULL;
inline constexpr std::uint32_t standing_rest_header = 32;
inline constexpr std::uint32_t standing_organ_octets = 32;

namespace standing_rest_law {

HOLONICS_CALLABLE constexpr void put(
    unsigned char* image, std::uint32_t at, std::uint64_t value) noexcept {
  for (std::uint32_t octet = 0; octet < 8U; ++octet) {
    image[at + octet] = static_cast<unsigned char>((value >> (octet * 8U)) & 0xFFU);
  }
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t take(
    const unsigned char* image, std::uint32_t at) noexcept {
  std::uint64_t value = 0;
  for (std::uint32_t octet = 0; octet < 8U; ++octet) {
    value |= static_cast<std::uint64_t>(image[at + octet]) << (octet * 8U);
  }
  return value;
}

/// The extent this standing rests to. **Variable, and proportional to the
/// derived population** — the whole reason this exists. A fixed-size summary
/// cannot make remounting cheaper than re-deriving; it can only make it equal.
template<class Standing>
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t rest_extent(
    const Standing& body) noexcept {
  return standing_rest_header + (body.standing() * standing_organ_octets) +
      (body.words_used() * 8U);
}

/// Rest the standing whole: every organ and every exact word it deposited.
///
/// **Each organ carries its own words immediately after its record.** A layout
/// that grouped all records and then all words would move every word whenever an
/// organ was founded, so nothing before the growth would stay put and no append
/// could be recognised. Here growth happens only at the end, which is the
/// property `base_address_unchanged` grades in the source owner.
template<class Standing>
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint32_t encode(
    const Standing& body, unsigned char* image, std::uint32_t capacity) noexcept {
  const std::uint32_t extent = rest_extent(body);
  if (image == nullptr || capacity < extent) {
    return 0;
  }
  put(image, 0, standing_rest_schema);
  put(image, 8, body.standing());
  put(image, 16, body.words_used());
  put(image, 24, body.revision());
  std::uint32_t at = standing_rest_header;
  for (std::uint32_t slot = 0; slot < body.standing(); ++slot) {
    const auto* organ = body.at(slot);
    put(image, at, organ->identity.value());
    put(image, at + 8, organ->caused_by.value());
    put(image, at + 16, 0);
    put(image, at + 24, organ->word_count);
    at = at + standing_organ_octets;
    for (std::uint32_t held = 0; held < organ->word_count; ++held) {
      put(image, at, body.word_at(*organ, held));
      at = at + 8U;
    }
  }
  return extent;
}

/// Found a fresh standing from the rested octets alone. No source, no card, no
/// developmental population is consulted, and nothing is re-derived.
template<class Standing>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool decode(
    Standing& body, const unsigned char* image, std::uint32_t extent) noexcept {
  if (image == nullptr || extent < standing_rest_header ||
      take(image, 0) != standing_rest_schema) {
    return false;
  }
  const auto organs = static_cast<std::uint32_t>(take(image, 8));
  const auto words = static_cast<std::uint32_t>(take(image, 16));
  if (extent < standing_rest_header + (organs * standing_organ_octets) + (words * 8U)) {
    return false;
  }
  std::uint32_t at = standing_rest_header;
  for (std::uint32_t slot = 0; slot < organs; ++slot) {
    returned_organ organ{};
    organ.identity = exact::word{take(image, at)};
    organ.caused_by = exact::word{take(image, at + 8)};
    const auto count = static_cast<std::uint32_t>(take(image, at + 24));
    at = at + standing_organ_octets;
    std::uint64_t carried[64]{};
    if (count > 64U || at + (count * 8U) > extent) {
      return false;
    }
    for (std::uint32_t held = 0; held < count; ++held) {
      carried[held] = take(image, at + (held * 8U));
    }
    at = at + (count * 8U);
    if (!body.try_restore(organ, carried, count)) {
      return false;
    }
  }
  return true;
}

/// Are these two standings the same body? Organ for organ and word for word.
/// **This is the exact logical comparison a revision key may never replace.**
template<class Standing>
[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_standing(
    const Standing& left, const Standing& right) noexcept {
  if (left.standing() != right.standing() || left.words_used() != right.words_used()) {
    return false;
  }
  for (std::uint32_t slot = 0; slot < left.standing(); ++slot) {
    const auto* one = left.at(slot);
    const auto* other = right.at(slot);
    if (one->identity != other->identity || one->caused_by != other->caused_by ||
        one->word_count != other->word_count) {
      return false;
    }
    for (std::uint32_t held = 0; held < one->word_count; ++held) {
      if (left.word_at(*one, held) != right.word_at(*other, held)) {
        return false;
      }
    }
  }
  return true;
}

}  // namespace standing_rest_law

}  // namespace holonics::body
