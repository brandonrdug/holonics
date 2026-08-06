#pragma once

#include <cstdint>

#include <holonics/exact/status.hpp>

namespace holonics::exact {

/// An exact dyadic value `numerator / 2^exponent`.
///
/// The carrier is exact. It is never rounded and never approximates: every
/// admitted operation either returns an exact dyadic or refuses with a typed
/// receipt naming the exponent it would have required.
struct dyadic final {
  std::int64_t numerator{};
  std::uint8_t exponent{};
};

/// Declared exponent aperture. Beyond it the homogeneous integer evaluation in
/// `enclosure.hpp` can no longer prove its own products in range, so refinement
/// refuses instead of continuing.
inline constexpr std::uint8_t dyadic_exponent_ceiling = 40;
inline constexpr std::int64_t dyadic_magnitude_ceiling = std::int64_t{1} << 41;

namespace dyadic_law {

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t magnitude(
    std::int64_t value) noexcept {
  return value < 0 ? -value : value;
}

/// Two's-complement magnitude taken in unsigned arithmetic, so the extreme
/// negative value has no undefined negation.
[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t unsigned_magnitude(
    std::int64_t value) noexcept {
  return value < 0 ? (~static_cast<std::uint64_t>(value) + 1U)
                   : static_cast<std::uint64_t>(value);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t bit_length(
    std::int64_t value) noexcept {
  std::uint64_t remaining = unsigned_magnitude(value);
  std::uint8_t length = 0;
  while (remaining != 0) {
    remaining >>= 1U;
    ++length;
  }
  return length;
}

/// Division-free product admission. No integer division appears anywhere in the
/// device-reachable cone: the compiler's 64-bit division helper reaches a
/// floating reciprocal on this architecture, which the binary audit refuses.
/// The test is conservative by construction; a rejected borderline product is a
/// declared aperture, never a wrapped value.
[[nodiscard]] HOLONICS_CALLABLE constexpr bool product_fits(
    std::int64_t left,
    std::int64_t right) noexcept {
  return static_cast<unsigned>(bit_length(left)) +
      static_cast<unsigned>(bit_length(right)) <= 62U;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool shift_fits(
    std::int64_t value,
    std::uint8_t shift) noexcept {
  return shift < 62U &&
      static_cast<unsigned>(bit_length(value)) + static_cast<unsigned>(shift) <= 62U;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool admitted(dyadic value) noexcept {
  return value.exponent <= dyadic_exponent_ceiling &&
      magnitude(value.numerator) <= dyadic_magnitude_ceiling;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr dyadic from_integer(
    std::int64_t value) noexcept {
  return dyadic{value, 0};
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int8_t sign(dyadic value) noexcept {
  if (value.numerator > 0) {
    return 1;
  }
  return value.numerator < 0 ? static_cast<std::int8_t>(-1) : static_cast<std::int8_t>(0);
}

/// Re-express `value` at a coarser-denominator exponent without changing it.
/// Refuses rather than shifting a numerator out of the declared aperture.
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<dyadic> promote(
    dyadic value,
    std::uint8_t exponent) noexcept {
  checked_result<dyadic> result{};
  result.receipt.admitted_limbs = dyadic_exponent_ceiling;
  result.receipt.required_limbs = exponent;
  if (!admitted(value) || exponent < value.exponent ||
      exponent > dyadic_exponent_ceiling) {
    result.receipt.state = status::capacity_refused;
    return result;
  }
  const auto shift = static_cast<std::uint8_t>(exponent - value.exponent);
  if (magnitude(value.numerator) > (dyadic_magnitude_ceiling >> shift)) {
    result.receipt.state = status::capacity_refused;
    return result;
  }
  result.value = dyadic{value.numerator << shift, exponent};
  return result;
}

/// Exact order. Returns `-1`, `0`, or `1` for left against right.
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<std::int8_t> compare(
    dyadic left,
    dyadic right) noexcept {
  checked_result<std::int8_t> result{};
  const std::uint8_t shared =
      left.exponent > right.exponent ? left.exponent : right.exponent;
  const auto promoted_left = promote(left, shared);
  const auto promoted_right = promote(right, shared);
  if (!promoted_left.accepted()) {
    result.receipt = promoted_left.receipt;
    return result;
  }
  if (!promoted_right.accepted()) {
    result.receipt = promoted_right.receipt;
    return result;
  }
  result.receipt.admitted_limbs = dyadic_exponent_ceiling;
  result.receipt.required_limbs = shared;
  if (promoted_left.value.numerator > promoted_right.value.numerator) {
    result.value = 1;
  } else if (promoted_left.value.numerator < promoted_right.value.numerator) {
    result.value = -1;
  }
  return result;
}

/// The exact arithmetic midpoint. This is the only refinement transport; it
/// introduces one further exponent and never selects a nearby representable
/// point.
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<dyadic> midpoint(
    dyadic left,
    dyadic right) noexcept {
  checked_result<dyadic> result{};
  const std::uint8_t shared =
      left.exponent > right.exponent ? left.exponent : right.exponent;
  if (shared >= dyadic_exponent_ceiling) {
    result.receipt.admitted_limbs = dyadic_exponent_ceiling;
    result.receipt.required_limbs = static_cast<std::uint16_t>(shared + 1U);
    result.receipt.state = status::capacity_refused;
    return result;
  }
  const auto promoted_left = promote(left, shared);
  const auto promoted_right = promote(right, shared);
  if (!promoted_left.accepted()) {
    result.receipt = promoted_left.receipt;
    return result;
  }
  if (!promoted_right.accepted()) {
    result.receipt = promoted_right.receipt;
    return result;
  }
  const std::int64_t sum =
      promoted_left.value.numerator + promoted_right.value.numerator;
  if (magnitude(sum) > dyadic_magnitude_ceiling) {
    result.receipt.admitted_limbs = dyadic_exponent_ceiling;
    result.receipt.state = status::capacity_refused;
    return result;
  }
  result.receipt.admitted_limbs = dyadic_exponent_ceiling;
  result.receipt.required_limbs = static_cast<std::uint16_t>(shared + 1U);
  result.value = dyadic{sum, static_cast<std::uint8_t>(shared + 1U)};
  return result;
}

/// Exact comparison of `|value|` against the rational `bound_numerator /
/// bound_denominator`, both strictly positive. Returns `-1` when the magnitude
/// is strictly below the bound.
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<std::int8_t>
compare_magnitude(
    dyadic value,
    std::int64_t bound_numerator,
    std::int64_t bound_denominator) noexcept {
  checked_result<std::int8_t> result{};
  result.receipt.admitted_limbs = dyadic_exponent_ceiling;
  if (!admitted(value) || bound_numerator <= 0 || bound_denominator <= 0) {
    result.receipt.state = status::capacity_refused;
    return result;
  }
  const std::int64_t scaled_magnitude = magnitude(value.numerator);
  if (!product_fits(scaled_magnitude, bound_denominator) ||
      !shift_fits(bound_numerator, value.exponent)) {
    result.receipt.state = status::capacity_refused;
    return result;
  }
  const std::int64_t left = scaled_magnitude * bound_denominator;
  const std::int64_t right = bound_numerator << value.exponent;
  if (left > right) {
    result.value = 1;
  } else if (left < right) {
    result.value = -1;
  }
  return result;
}

}  // namespace dyadic_law
}  // namespace holonics::exact
