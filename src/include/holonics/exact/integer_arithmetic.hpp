#pragma once

#include <cstddef>
#include <cstdint>

#include <holonics/exact/integer.hpp>

namespace holonics::exact {

struct wide_product final {
  std::uint64_t low{};
  std::uint64_t high{};
};

[[nodiscard]] HOLONICS_CALLABLE constexpr wide_product multiply_words(
    std::uint64_t left,
    std::uint64_t right) noexcept {
  constexpr std::uint64_t mask = 0xffff'ffffU;
  const std::uint64_t left_low = left & mask;
  const std::uint64_t left_high = left >> 32U;
  const std::uint64_t right_low = right & mask;
  const std::uint64_t right_high = right >> 32U;

  const std::uint64_t low_low = left_low * right_low;
  const std::uint64_t low_high = left_low * right_high;
  const std::uint64_t high_low = left_high * right_low;
  const std::uint64_t high_high = left_high * right_high;

  const std::uint64_t middle =
      (low_low >> 32U) + (low_high & mask) + (high_low & mask);
  return wide_product{
      (low_low & mask) | (middle << 32U),
      high_high + (low_high >> 32U) + (high_low >> 32U) + (middle >> 32U)};
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<unsigned_integer<Capacity>> add(
    const unsigned_integer<Capacity>& left,
    const unsigned_integer<Capacity>& right) noexcept {
  checked_result<unsigned_integer<Capacity>> result{};
  result.receipt.admitted_limbs = static_cast<std::uint16_t>(Capacity);
  const std::size_t limit = left.used() > right.used() ? left.used() : right.used();
  std::uint64_t carry = 0;
  for (std::size_t index = 0; index < limit; ++index) {
    const std::uint64_t a = left.limb(index);
    const std::uint64_t b = right.limb(index);
    const std::uint64_t first = a + b;
    const std::uint64_t carry_first = first < a ? 1U : 0U;
    const std::uint64_t second = first + carry;
    const std::uint64_t carry_second = second < first ? 1U : 0U;
    result.value.set_limb(index, second);
    carry = carry_first | carry_second;
  }
  if (carry != 0) {
    result.receipt.required_limbs = static_cast<std::uint16_t>(limit + 1);
    if (limit == Capacity) {
      result.value.clear();
      result.receipt.state = status::capacity_refused;
      return result;
    }
    result.value.set_limb(limit, carry);
  }
  result.receipt.required_limbs = static_cast<std::uint16_t>(result.value.used());
  return result;
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<unsigned_integer<Capacity>> subtract(
    const unsigned_integer<Capacity>& left,
    const unsigned_integer<Capacity>& right) noexcept {
  checked_result<unsigned_integer<Capacity>> result{};
  result.receipt.admitted_limbs = static_cast<std::uint16_t>(Capacity);
  if (compare(left, right) < 0) {
    result.receipt.state = status::negative_refused;
    return result;
  }
  std::uint64_t borrow = 0;
  for (std::size_t index = 0; index < left.used(); ++index) {
    const std::uint64_t a = left.limb(index);
    const std::uint64_t b = right.limb(index);
    const std::uint64_t first = a - b;
    const std::uint64_t borrow_first = a < b ? 1U : 0U;
    const std::uint64_t second = first - borrow;
    const std::uint64_t borrow_second = first < borrow ? 1U : 0U;
    result.value.set_limb(index, second);
    borrow = borrow_first | borrow_second;
  }
  result.value.normalize();
  result.receipt.required_limbs = static_cast<std::uint16_t>(result.value.used());
  return result;
}

template<std::size_t Capacity>
HOLONICS_CALLABLE constexpr bool add_at(
    unsigned_integer<Capacity>& value,
    std::size_t index,
    std::uint64_t addend) noexcept {
  while (addend != 0 && index < Capacity) {
    const std::uint64_t before = value.limb(index);
    const std::uint64_t after = before + addend;
    value.set_limb(index, after);
    addend = after < before ? 1U : 0U;
    ++index;
  }
  return addend == 0;
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<unsigned_integer<Capacity>> multiply(
    const unsigned_integer<Capacity>& left,
    const unsigned_integer<Capacity>& right) noexcept {
  checked_result<unsigned_integer<Capacity>> result{};
  result.receipt.admitted_limbs = static_cast<std::uint16_t>(Capacity);
  if (left.is_zero() || right.is_zero()) {
    return result;
  }
  for (std::size_t left_index = 0; left_index < left.used(); ++left_index) {
    for (std::size_t right_index = 0; right_index < right.used(); ++right_index) {
      const std::size_t output_index = left_index + right_index;
      const wide_product product = multiply_words(
          left.limb(left_index), right.limb(right_index));
      if (output_index >= Capacity ||
          !add_at(result.value, output_index, product.low) ||
          (product.high != 0 &&
           (output_index + 1 >= Capacity ||
            !add_at(result.value, output_index + 1, product.high)))) {
        result.value.clear();
        result.receipt.state = status::capacity_refused;
        const std::size_t required = left.used() + right.used();
        result.receipt.required_limbs = static_cast<std::uint16_t>(
            required > 65'535 ? 65'535 : required);
        return result;
      }
    }
  }
  result.value.normalize();
  result.receipt.required_limbs = static_cast<std::uint16_t>(result.value.used());
  return result;
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr checked_result<unsigned_integer<Capacity>> shift_left(
    const unsigned_integer<Capacity>& value,
    std::size_t amount) noexcept {
  checked_result<unsigned_integer<Capacity>> result{};
  result.receipt.admitted_limbs = static_cast<std::uint16_t>(Capacity);
  if (value.is_zero()) {
    return result;
  }
  const std::size_t word_shift = amount / 64;
  const std::size_t bit_shift = amount % 64;
  const std::size_t required_bits = value.bit_length() + amount;
  const std::size_t required_limbs = (required_bits + 63) / 64;
  result.receipt.required_limbs = static_cast<std::uint16_t>(
      required_limbs > 65'535 ? 65'535 : required_limbs);
  if (required_limbs > Capacity) {
    result.receipt.state = status::capacity_refused;
    return result;
  }
  for (std::size_t index = 0; index < value.used(); ++index) {
    const std::size_t destination = index + word_shift;
    result.value.set_limb(destination, result.value.limb(destination) |
        (value.limb(index) << bit_shift));
    if (bit_shift != 0 && destination + 1 < Capacity) {
      result.value.set_limb(destination + 1, result.value.limb(destination + 1) |
          (value.limb(index) >> (64 - bit_shift)));
    }
  }
  result.value.normalize();
  return result;
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr unsigned_integer<Capacity> shift_right(
    const unsigned_integer<Capacity>& value,
    std::size_t amount) noexcept {
  unsigned_integer<Capacity> result{};
  const std::size_t word_shift = amount / 64;
  const std::size_t bit_shift = amount % 64;
  if (word_shift >= value.used()) {
    return result;
  }
  for (std::size_t index = word_shift; index < value.used(); ++index) {
    const std::size_t destination = index - word_shift;
    std::uint64_t part = value.limb(index) >> bit_shift;
    if (bit_shift != 0 && index + 1 < value.used()) {
      part |= value.limb(index + 1) << (64 - bit_shift);
    }
    result.set_limb(destination, part);
  }
  result.normalize();
  return result;
}

}  // namespace holonics::exact
