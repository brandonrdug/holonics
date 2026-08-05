#pragma once

#include <cstdint>

#include <holonics/organ/arithmetic_spectral_law.hpp>

namespace holonics::organ::arithmetic_test_detail {

[[nodiscard]] HOLONICS_CALLABLE inline gaussian_integer add(
    gaussian_integer left, gaussian_integer right) noexcept {
  return {left.real + right.real, left.imaginary + right.imaginary};
}

[[nodiscard]] HOLONICS_CALLABLE inline gaussian_integer multiply(
    gaussian_integer left, gaussian_integer right) noexcept {
  return {left.real * right.real - left.imaginary * right.imaginary,
      left.real * right.imaginary + left.imaginary * right.real};
}

[[nodiscard]] HOLONICS_CALLABLE inline gaussian_integer power(
    gaussian_integer base, std::uint8_t exponent) noexcept {
  gaussian_integer result{1,0};
  while (exponent != 0) {
    if ((exponent & 1U) != 0) { result = multiply(result, base); }
    exponent >>= 1U;
    if (exponent != 0) { base = multiply(base, base); }
  }
  return result;
}

[[nodiscard]] HOLONICS_CALLABLE inline std::int8_t coefficient(
    std::uint32_t code, std::uint8_t slot) noexcept {
  for (std::uint8_t index = 0; index < slot; ++index) {
    code = static_cast<std::uint32_t>(exact::divide_unsigned(code, 3U).quotient);
  }
  return static_cast<std::int8_t>(exact::divide_unsigned(code, 3U).remainder) - 1;
}

HOLONICS_CALLABLE inline void trace_current(const arithmetic_curve_receipt& curve,
    std::uint8_t curve_index, std::uint8_t current, trace_current_receipt& out) noexcept {
  out.curve = curve_index;
  for (std::uint8_t degree = 1; degree <= arithmetic_degree_count; ++degree) {
    const auto index = static_cast<std::uint8_t>(degree - 1U);
    const auto c = coefficient(current, index); out.coefficient[index] = c;
    const auto p_power = arithmetic_field_detail::power_u32(curve.source.prime, degree);
    std::uint32_t place = 0;
    for (std::uint8_t divisor = 1; divisor <= degree; ++divisor) {
      if (exact::divide_unsigned(degree, divisor).remainder == 0) {
        place += divisor * curve.closed_places[divisor - 1U];
      }
    }
    out.place_side += static_cast<std::int64_t>(c) * place;
    out.normalization_side += static_cast<std::int64_t>(c) * (1 + p_power);
    out.spectral_side += static_cast<std::int64_t>(c) * curve.power_traces[degree];
  }
  out.residual = out.place_side - out.normalization_side + out.spectral_side;
  out.lineage = exact::word{curve.lineage.value() + 600'000U + current};
}

HOLONICS_CALLABLE inline void norm_current(const arithmetic_curve_receipt& curve,
    std::uint8_t curve_index, std::uint16_t current, norm_current_receipt& out) noexcept {
  out.curve = curve_index; const auto pi = curve.frobenius;
  const gaussian_integer conjugate{pi.real,-pi.imaginary};
  for (std::uint8_t slot = 0; slot <= arithmetic_degree_count; ++slot) {
    const auto c = coefficient(current, slot); out.coefficient[slot] = c;
    auto term = multiply(power(pi, slot), power(conjugate, arithmetic_degree_count - slot));
    term.real *= c; term.imaginary *= c; out.value = add(out.value, term);
  }
  out.norm = out.value.real * out.value.real + out.value.imaginary * out.value.imaginary;
  out.nonnegative = out.norm >= 0;
  out.lineage = exact::word{curve.lineage.value() + 700'000U + current};
}

}  // namespace holonics::organ::arithmetic_test_detail
