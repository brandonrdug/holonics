#pragma once

#include <holonics/organ/blind_integer_exact.hpp>
#include <holonics/organ/cm_incidence_receipt.hpp>

namespace holonics::organ::cm_arithmetic_detail {

[[nodiscard]] HOLONICS_CALLABLE constexpr bool equal(
    const cm_element& left, const cm_element& right) noexcept {
  for (std::uint8_t slot = 0; slot < cm_degree_capacity; ++slot) {
    if (left.coefficients[slot] != right.coefficients[slot]) { return false; }
  }
  return true;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr cm_element one() noexcept {
  cm_element out{};
  out.coefficients[0] = 1;
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr cm_element generator() noexcept {
  cm_element out{};
  out.coefficients[1] = 1;
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr cm_element negate(
    const cm_element& value) noexcept {
  cm_element out{};
  for (std::uint8_t slot = 0; slot < cm_degree_capacity; ++slot) {
    out.coefficients[slot] = -value.coefficients[slot];
  }
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr cm_element subtract(
    const cm_element& left, const cm_element& right, bool& exact) noexcept {
  cm_element out{};
  for (std::uint8_t slot = 0; slot < cm_degree_capacity; ++slot) {
    exact = exact && blind_integer_detail::subtract(
        left.coefficients[slot], right.coefficients[slot], out.coefficients[slot]);
  }
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr cm_element add(
    const cm_element& left, const cm_element& right, bool& exact) noexcept {
  cm_element out{};
  for (std::uint8_t slot = 0; slot < cm_degree_capacity; ++slot) {
    exact = exact && blind_integer_detail::add(
        left.coefficients[slot], right.coefficients[slot], out.coefficients[slot]);
  }
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr cm_element conjugate(
    const cm_element& value, bool& exact) noexcept {
  cm_element out{};
  exact = exact && blind_integer_detail::subtract(
      value.coefficients[0], value.coefficients[1], out.coefficients[0]);
  out.coefficients[1] = -value.coefficients[1];
  exact = exact && blind_integer_detail::subtract(
      value.coefficients[3], value.coefficients[1], out.coefficients[2]) &&
      blind_integer_detail::subtract(
          value.coefficients[2], value.coefficients[1], out.coefficients[3]);
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr cm_element multiply(
    const cm_element& left, const cm_element& right, bool& exact) noexcept {
  std::int64_t raw[7]{};
  for (std::uint8_t i = 0; i < cm_degree_capacity; ++i) {
    for (std::uint8_t j = 0; j < cm_degree_capacity; ++j) {
      std::int64_t product = 0;
      std::int64_t sum = 0;
      exact = exact && blind_integer_detail::multiply(
          left.coefficients[i], right.coefficients[j], product) &&
          blind_integer_detail::add(raw[i + j], product, sum);
      raw[i + j] = sum;
    }
  }
  cm_element out{};
  std::int64_t held = 0;
  exact = exact && blind_integer_detail::subtract(raw[0], raw[4], held) &&
      blind_integer_detail::add(held, raw[5], out.coefficients[0]) &&
      blind_integer_detail::subtract(raw[1], raw[4], held) &&
      blind_integer_detail::add(held, raw[6], out.coefficients[1]) &&
      blind_integer_detail::subtract(raw[2], raw[4], out.coefficients[2]) &&
      blind_integer_detail::subtract(raw[3], raw[4], out.coefficients[3]);
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr cm_element norm(
    const cm_element& value, bool& exact) noexcept {
  return multiply(value, conjugate(value, exact), exact);
}

[[nodiscard]] HOLONICS_CALLABLE constexpr cm_element point(std::uint8_t vertex) noexcept {
  cm_element out{};
  for (std::uint8_t slot = 0; slot < cm_degree_capacity; ++slot) {
    out.coefficients[slot] = static_cast<std::int64_t>((vertex >> slot) & 1U);
  }
  return out;
}

[[nodiscard]] HOLONICS_CALLABLE constexpr std::uint8_t residue_mask(
    const cm_element& value) noexcept {
  std::uint8_t mask = 0;
  for (std::uint8_t slot = 0; slot < cm_degree_capacity; ++slot) {
    const auto parity = static_cast<std::uint64_t>(value.coefficients[slot]) & 1U;
    mask = static_cast<std::uint8_t>(mask | static_cast<std::uint8_t>(parity << slot));
  }
  return mask;
}

}  // namespace holonics::organ::cm_arithmetic_detail
