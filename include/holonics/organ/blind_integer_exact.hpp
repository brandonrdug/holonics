#pragma once

#include <cstdint>

#include <holonics/organ/blind_reconstruction_receipt.hpp>

namespace holonics::organ::blind_integer_detail {

inline constexpr std::int64_t exact_limit = 9'223'372'036'854'775'807LL;

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint64_t magnitude(
    std::int64_t value) noexcept {
  return value < 0 ? static_cast<std::uint64_t>(-(value + 1)) + 1U :
      static_cast<std::uint64_t>(value);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool divide_unsigned(
    std::uint64_t dividend, std::uint64_t divisor, std::uint64_t& quotient,
    std::uint64_t& remainder) noexcept {
  quotient = 0;
  remainder = 0;
  if (divisor == 0) { return false; }
  for (std::uint8_t offset = 64; offset > 0; --offset) {
    const auto bit = static_cast<std::uint8_t>(offset - 1U);
    const bool carried = (remainder & (std::uint64_t{1} << 63U)) != 0;
    remainder = (remainder << 1U) | ((dividend >> bit) & 1U);
    if (carried || remainder >= divisor) {
      remainder -= divisor;
      quotient |= std::uint64_t{1} << bit;
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool divide(
    std::int64_t dividend, std::int64_t divisor, std::int64_t& quotient,
    std::int64_t& remainder) noexcept {
  std::uint64_t unsigned_quotient = 0;
  std::uint64_t unsigned_remainder = 0;
  if (!divide_unsigned(magnitude(dividend), magnitude(divisor), unsigned_quotient,
          unsigned_remainder) ||
      unsigned_quotient > static_cast<std::uint64_t>(exact_limit) ||
      unsigned_remainder > static_cast<std::uint64_t>(exact_limit)) { return false; }
  quotient = (dividend < 0) != (divisor < 0) ?
      -static_cast<std::int64_t>(unsigned_quotient) :
      static_cast<std::int64_t>(unsigned_quotient);
  remainder = dividend < 0 ? -static_cast<std::int64_t>(unsigned_remainder) :
      static_cast<std::int64_t>(unsigned_remainder);
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool divide_exact(
    std::int64_t dividend, std::int64_t divisor, std::int64_t& quotient) noexcept {
  std::int64_t remainder = 0;
  return divide(dividend, divisor, quotient, remainder) && remainder == 0;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool add(
    std::int64_t left, std::int64_t right, std::int64_t& out) noexcept {
  if ((right > 0 && left > exact_limit - right) ||
      (right < 0 && left < -exact_limit - right)) { return false; }
  out = left + right;
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool subtract(
    std::int64_t left, std::int64_t right, std::int64_t& out) noexcept {
  if (right == -exact_limit) { return false; }
  return add(left, -right, out);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool multiply(
    std::int64_t left, std::int64_t right, std::int64_t& out) noexcept {
  std::uint64_t addend = magnitude(left);
  std::uint64_t remaining = magnitude(right);
  std::uint64_t product = 0;
  constexpr auto limit = static_cast<std::uint64_t>(exact_limit);
  while (remaining != 0) {
    if ((remaining & 1U) != 0) {
      if (addend > limit - product) { return false; }
      product += addend;
    }
    remaining >>= 1U;
    if (remaining != 0) {
      if (addend > limit - addend) { return false; }
      addend += addend;
    }
  }
  out = (left < 0) != (right < 0) ? -static_cast<std::int64_t>(product) :
      static_cast<std::int64_t>(product);
  return true;
}

template<std::size_t Capacity>
[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t determinant(
    const std::int64_t (&source)[Capacity][Capacity], std::uint8_t size,
    bool& exact) noexcept {
  if (size == 0 || size > Capacity) { exact = false; return 0; }
  std::int64_t matrix[Capacity][Capacity]{};
  for (std::uint8_t row = 0; row < size; ++row) {
    for (std::uint8_t column = 0; column < size; ++column) {
      matrix[row][column] = source[row][column];
    }
  }
  std::int64_t previous = 1;
  bool negative = false;
  exact = true;
  for (std::uint8_t pivot = 0; pivot + 1U < size; ++pivot) {
    if (matrix[pivot][pivot] == 0) {
      std::uint8_t replacement = static_cast<std::uint8_t>(pivot + 1U);
      while (replacement < size && matrix[replacement][pivot] == 0) { ++replacement; }
      if (replacement == size) { return 0; }
      for (std::uint8_t column = 0; column < size; ++column) {
        const auto held = matrix[pivot][column];
        matrix[pivot][column] = matrix[replacement][column];
        matrix[replacement][column] = held;
      }
      negative = !negative;
    }
    const auto diagonal = matrix[pivot][pivot];
    for (std::uint8_t row = static_cast<std::uint8_t>(pivot + 1U); row < size; ++row) {
      for (std::uint8_t column = static_cast<std::uint8_t>(pivot + 1U);
          column < size; ++column) {
        std::int64_t first = 0;
        std::int64_t second = 0;
        std::int64_t numerator = 0;
        std::int64_t quotient = 0;
        exact = exact && multiply(matrix[row][column], diagonal, first) &&
            multiply(matrix[row][pivot], matrix[pivot][column], second) &&
            subtract(first, second, numerator) &&
            divide_exact(numerator, previous, quotient);
        if (!exact) { return 0; }
        matrix[row][column] = quotient;
      }
    }
    previous = diagonal;
  }
  const auto value = matrix[size - 1U][size - 1U];
  return negative ? -value : value;
}

}  // namespace holonics::organ::blind_integer_detail
