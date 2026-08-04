#pragma once

#include <cstdint>

#include <holonics/organ/blind_integer_exact.hpp>

namespace holonics::organ::blind_code_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t popcount(std::uint8_t value) noexcept {
  std::uint8_t count = 0;
  while (value != 0) {
    count = static_cast<std::uint8_t>(count + (value & 1U));
    value = static_cast<std::uint8_t>(value >> 1U);
  }
  return count;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint16_t choose(
    std::uint8_t n, std::uint8_t k) noexcept {
  if (k > n) { return 0; }
  if (k > static_cast<std::uint8_t>(n - k)) { k = static_cast<std::uint8_t>(n - k); }
  std::uint32_t value = 1;
  for (std::uint8_t step = 1; step <= k; ++step) {
    const auto product = static_cast<std::uint64_t>(value) *
        static_cast<std::uint32_t>(n - k + step);
    std::uint64_t quotient = 0;
    std::uint64_t remainder = 0;
    if (!blind_integer_detail::divide_unsigned(product, step, quotient, remainder) ||
        remainder != 0 || quotient > 65'535U) { return 0; }
    value = static_cast<std::uint32_t>(quotient);
  }
  return static_cast<std::uint16_t>(value);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::int64_t krawtchouk(
    std::uint8_t n, std::uint8_t degree, std::uint8_t position) noexcept {
  std::int64_t value = 0;
  for (std::uint8_t left = 0; left <= degree; ++left) {
    if (left > position || degree - left > n - position) { continue; }
    const auto term = static_cast<std::int64_t>(choose(position, left)) *
        static_cast<std::int64_t>(choose(static_cast<std::uint8_t>(n - position),
            static_cast<std::uint8_t>(degree - left)));
    value += (left & 1U) == 0 ? term : -term;
  }
  return value;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool belongs(
    const binary_code_problem_card& card, std::uint8_t word) noexcept {
  for (std::uint8_t row = 0; row < card.row_count; ++row) {
    if ((popcount(static_cast<std::uint8_t>(word & card.parity_rows[row])) & 1U) != 0) {
      return false;
    }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t cell_of(
    std::uint8_t word, std::uint8_t target, std::uint8_t dimension,
    std::uint8_t right_size) noexcept {
  const auto mask = static_cast<std::uint8_t>((1U << dimension) - 1U);
  const auto left = popcount(static_cast<std::uint8_t>(word & target));
  const auto right = popcount(static_cast<std::uint8_t>(word & mask & ~target));
  return static_cast<std::uint8_t>(left * right_size + right);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr bool same_factor(
    const pair_incidence_receipt& first, const pair_incidence_receipt& second) noexcept {
  if (first.cell_count != second.cell_count) { return false; }
  for (std::uint8_t slot = 0; slot < blind_distance_capacity; ++slot) {
    if (first.characteristic_roots[slot] != second.characteristic_roots[slot] ||
        first.characteristic_multiplicity[slot] !=
            second.characteristic_multiplicity[slot]) { return false; }
  }
  return true;
}

}  // namespace holonics::organ::blind_code_detail
