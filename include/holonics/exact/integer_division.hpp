#pragma once

#include <cstddef>

#include <holonics/exact/integer_arithmetic.hpp>

namespace holonics::exact {

template<std::size_t Capacity>
struct division_result final {
  unsigned_integer<Capacity> quotient{};
  unsigned_integer<Capacity> remainder{};
  operation_receipt receipt{};

  [[nodiscard]] HOLONICS_CALLABLE constexpr bool accepted() const noexcept {
    return receipt.accepted();
  }
};

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr division_result<Capacity> divide(
    const unsigned_integer<Capacity>& dividend,
    const unsigned_integer<Capacity>& divisor) noexcept {
  division_result<Capacity> result{};
  result.receipt.admitted_limbs = static_cast<std::uint16_t>(Capacity);
  if (divisor.is_zero()) {
    result.receipt.state = status::divide_by_zero;
    return result;
  }
  result.remainder = dividend;
  if (compare(dividend, divisor) < 0) {
    result.receipt.required_limbs = static_cast<std::uint16_t>(dividend.used());
    return result;
  }

  const std::size_t displacement = dividend.bit_length() - divisor.bit_length();
  const auto shifted = shift_left(divisor, displacement);
  if (!shifted.accepted()) {
    result.receipt = shifted.receipt;
    return result;
  }
  unsigned_integer<Capacity> trial = shifted.value;
  for (std::size_t step = displacement + 1; step != 0; --step) {
    const std::size_t bit_index = step - 1;
    if (compare(result.remainder, trial) >= 0) {
      const auto difference = subtract(result.remainder, trial);
      result.remainder = difference.value;
      const std::size_t limb_index = bit_index / 64;
      const std::size_t position = bit_index % 64;
      result.quotient.set_limb(
          limb_index,
          result.quotient.limb(limb_index) | (std::uint64_t{1} << position));
    }
    trial = shift_right(trial, 1);
  }
  result.quotient.normalize();
  result.remainder.normalize();
  result.receipt.required_limbs = static_cast<std::uint16_t>(result.quotient.used());
  return result;
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<unsigned_integer<Capacity>> greatest_common_divisor(
    unsigned_integer<Capacity> left,
    unsigned_integer<Capacity> right) noexcept {
  checked_result<unsigned_integer<Capacity>> result{};
  result.receipt.admitted_limbs = static_cast<std::uint16_t>(Capacity);
  while (!right.is_zero()) {
    const auto step = divide(left, right);
    if (!step.accepted()) {
      result.receipt = step.receipt;
      return result;
    }
    left = right;
    right = step.remainder;
  }
  result.value = left;
  result.receipt.required_limbs = static_cast<std::uint16_t>(left.used());
  return result;
}

template<std::size_t Destination, std::size_t Source>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<unsigned_integer<Destination>> promote(
    const unsigned_integer<Source>& value) noexcept {
  checked_result<unsigned_integer<Destination>> result{};
  result.receipt.admitted_limbs = static_cast<std::uint16_t>(Destination);
  result.receipt.required_limbs = static_cast<std::uint16_t>(value.used());
  if (value.used() > Destination) {
    result.receipt.state = status::capacity_refused;
    return result;
  }
  for (std::size_t index = 0; index < value.used(); ++index) {
    result.value.set_limb(index, value.limb(index));
  }
  return result;
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr word stable_hash(
    const unsigned_integer<Capacity>& value) noexcept {
  std::uint64_t hash = 14'695'981'039'346'656'037ULL;
  constexpr std::uint64_t prime = 1'099'511'628'211ULL;
  for (std::size_t index = 0; index < value.used(); ++index) {
    std::uint64_t limb = value.limb(index);
    for (std::size_t octet = 0; octet < 8; ++octet) {
      hash ^= limb & 255U;
      hash *= prime;
      limb >>= 8U;
    }
  }
  hash ^= static_cast<std::uint64_t>(value.used());
  hash *= prime;
  return word{hash};
}

}  // namespace holonics::exact
